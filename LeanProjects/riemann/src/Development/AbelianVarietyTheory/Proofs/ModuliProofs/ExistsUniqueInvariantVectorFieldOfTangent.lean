import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningFieldStructureStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.InvField

theorem pbT_pbT {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) {O₀ : X.Opens} {O₁ : Y.Opens} {O₂ : Z.Opens}
    (h₁ : O₁ ≤ g ⁻¹ᵁ O₀) (h₂ : O₂ ≤ f ⁻¹ᵁ O₁) (s : Γ(X, O₀)) :
    pbT f (pbT g s O₁) O₂ = pbT (f ≫ g) s O₂ := by
  rw [pbT_of_le g h₁, pbT_of_le f h₂, pbT_of_le (f ≫ g) (h₂.trans (f.preimage_mono h₁))]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_comp_appLE f g O₀ O₁ O₂ h₁ h₂)

theorem pbT_id {Y : Scheme.{0}} {O : Y.Opens} (s : Γ(Y, O)) : pbT (𝟙 Y) s O = s := by
  rw [pbT_of_le (𝟙 Y) (O := O) (O₀ := O) le_rfl]
  exact (congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_eq_app (𝟙 Y) (U := O))).trans rfl

theorem pbT_eq_app {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O : Y.Opens} (s : Γ(Y, O)) :
    pbT f s (f ⁻¹ᵁ O) = (f.app O).hom s := by
  rw [pbT_of_le f le_rfl, Scheme.Hom.appLE_eq_app]

theorem constFn_spMap {R S : Type} [CommRing R] [CommRing S] {Y : Scheme.{0}} (q : Y ⟶ Sp S) (φ : R →+* S)
    (O : Y.Opens) (a : R) : constFn (q ≫ spMap φ) O a = constFn q O (φ a) := by
  have h : (spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]; rfl
  have h2 := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  have h3 := congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE q (spMap φ) ⊤ ⊤ O (fun _ _ => trivial) (fun _ _ => trivial))
  rw [h] at h3
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2 h3
  unfold constFn
  rw [← h3, h2]

theorem constFn_mul {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R)
    (O : Y.Opens) (a b : R) : constFn q O (a * b) = constFn q O a * constFn q O b := by
  simp [constFn]

theorem constFn_zero {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R)
    (O : Y.Opens) : constFn q O 0 = 0 := by
  simp [constFn]

theorem aux {K : Type} [Field K] {Y Y' : Scheme.{0}} (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (ρ T : Y' ⟶ Y)
    (j : Y ⟶ Y') (hp : IsPullback ρ π q (spMap (algebraMap K (DualNumber K)))) (hρ : j ≫ ρ = 𝟙 Y)
    (hπ : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)) (hT : j ≫ T = 𝟙 Y) (hq : T ≫ q = ρ ≫ q)
    (P : (∀ W : Y.Opens, Γ(Y, W) → Γ(Y, W)) → Prop)
    (hP : ∀ dd, P dd ↔ ∀ (W : Y.Opens) (f : Γ(Y, W)), pbT T f (ρ ⁻¹ᵁ W) =
      pbT ρ f (ρ ⁻¹ᵁ W) + constFn π _ DualNumber.eps * pbT ρ (dd W f) (ρ ⁻¹ᵁ W)) :
    (∃ dd, P dd) ∧ ∀ dd, P dd → (∀ W f f', dd W (f + f') = dd W f + dd W f') ∧ (∀ W f f', dd W (f * f') = f * dd W f' + f' * dd W f) ∧ (∀ W W' (f : Γ(Y, W)), W' ≤ W → dd W' (rsT f W') = rsT (dd W f) W') ∧ (∀ W a, dd W (constFn q W a) = 0) ∧ ∀ dd', P dd' → dd' = dd := by
  obtain ⟨hO, -, hex⟩ := GlobalTheory.T.const_thickening_field_structure K Y Y' q π ρ j hp hρ hπ
  have hTW : ∀ W : Y.Opens, ρ ⁻¹ᵁ W ≤ T ⁻¹ᵁ W := fun W => by
    have := hO (T ⁻¹ᵁ W)
    rw [← Scheme.Hom.comp_preimage j T, hT, Scheme.Hom.id_preimage] at this
    exact this.le
  have hjW : ∀ W : Y.Opens, W ≤ j ⁻¹ᵁ (ρ ⁻¹ᵁ W) := fun W => by
    rw [← Scheme.Hom.comp_preimage, hρ, Scheme.Hom.id_preimage]
  have uniq : ∀ (W : Y.Opens) (a b b' : Γ(Y, W)),
      pbT ρ a (ρ ⁻¹ᵁ W) + constFn π _ DualNumber.eps * pbT ρ b (ρ ⁻¹ᵁ W) =
      pbT ρ a (ρ ⁻¹ᵁ W) + constFn π _ DualNumber.eps * pbT ρ b' (ρ ⁻¹ᵁ W) → b = b' := by
    intro W a b b' h
    simp only [pbT_eq_app] at h
    have := (hex W _).unique (y₁ := (a, b)) (y₂ := (a, b')) rfl h
    exact congrArg Prod.snd this
  have hee : ∀ O, constFn π O DualNumber.eps * constFn π O DualNumber.eps = 0 := fun O => by
    rw [← constFn_mul, DualNumber.eps_mul_eps, constFn_zero]
  refine ⟨?_, fun dd hd => ?_⟩
  · choose ab hab using fun W (f : Γ(Y, W)) => (hex W (pbT T f (ρ ⁻¹ᵁ W))).exists
    refine ⟨fun W f => (ab W f).2, (hP _).2 fun W f => ?_⟩
    have h := hab W f
    rw [← pbT_eq_app, ← pbT_eq_app] at h
    have h' := congrArg (fun s => pbT j s W) h
    simp only [pbT_add, pbT_mul] at h'
    rw [pbT_pbT j T (hTW W) (hjW W), pbT_pbT j ρ le_rfl (hjW W), hT, hρ, pbT_id, pbT_id,
      pbT_constFn π j (hjW W), hπ, constFn_spMap] at h'
    have e : (TrivSqZeroExt.fstHom K K K).toRingHom DualNumber.eps = 0 := by simp
    rw [e, constFn_zero, zero_mul, add_zero] at h'
    rw [h, ← h']
  · have hd' := (hP _).1 hd
    refine ⟨fun W f f' => uniq W (f + f') _ _ ?_, fun W f f' => uniq W (f * f') _ _ ?_,
      fun W W' f h => uniq W' (rsT f W') _ _ ?_, fun W a => uniq W (constFn q W a) _ _ ?_, fun dd' hd₁ => ?_⟩
    · rw [← hd', pbT_add, hd', hd', pbT_add, pbT_add]; ring
    · rw [← hd', pbT_mul, hd', hd', pbT_add, pbT_mul, pbT_mul, pbT_mul]
      linear_combination (pbT ρ (dd W f) (ρ ⁻¹ᵁ W) * pbT ρ (dd W f') (ρ ⁻¹ᵁ W)) * hee (ρ ⁻¹ᵁ W)
    · have h1 : ρ ⁻¹ᵁ W' ≤ ρ ⁻¹ᵁ W := ρ.preimage_mono h
      rw [← hd', pbT_rsT T h (hTW W'), pbT_rsT ρ h le_rfl, pbT_rsT ρ h le_rfl, ← rsT_pbT T (hTW W) h1, hd',
        rsT_add, rsT_mul, rsT_pbT ρ le_rfl h1, rsT_pbT ρ le_rfl h1, rsT_constFn π h1]
    · rw [← hd', pbT_constFn q T (hTW W), pbT_constFn q ρ le_rfl, hq, pbT_zero, mul_zero, add_zero]
    · funext W f
      exact uniq W f _ _ (((hP _).1 hd₁ W f).symm.trans (hd' W f))

theorem main : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (v : epsR K ⟶ A₀), IsTangent v → (∃ dd, IsInvDer v dd) ∧ ∀ dd, IsInvDer v dd → (∀ W f f', dd W (f + f') = dd W f + dd W f') ∧ (∀ W f f', dd W (f * f') = f * dd W f' + f' * dd W f) ∧ (∀ W W' (f : Γ(A₀.left, W)), W' ≤ W → dd W' (rsT f W') = rsT (dd W f) W') ∧ (∀ W a, dd W (constFn A₀.hom W a) = 0) ∧ ∀ dd', IsInvDer v dd' → dd' = dd := by
  intro K _ A₀ _ v hv
  let s : 𝟙_ (Over (Sp K)) ⟶ epsR K := Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change spMap _ ≫ spMap _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)
  have hs : s ≫ v = η[A₀] := Over.OverMorphism.ext hv
  let j : A₀ ⟶ epsR K ⊗ A₀ := lift (toUnit A₀ ≫ s) (𝟙 A₀)
  have hT : j ≫ ((fst (epsR K) A₀ ≫ v) * snd (epsR K) A₀) = 𝟙 A₀ := by
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd, Category.assoc, hs, ← Hom.one_def, _root_.one_mul]
  refine aux A₀.hom (fst (epsR K) A₀).left (snd (epsR K) A₀).left
    ((fst (epsR K) A₀ ≫ v) * snd (epsR K) A₀).left j.left ?_ ?_ ?_ ?_ ?_ (IsInvDer v) (fun _ => Iff.rfl)
  · exact (IsPullback.of_hasPullback (epsR K).hom A₀.hom).flip
  · rw [← Over.comp_left, lift_snd]; rfl
  · rw [← Over.comp_left, lift_fst, Over.comp_left, Over.toUnit_left]; rfl
  · rw [← Over.comp_left, hT]; rfl
  · rw [Over.w, Over.w]

end GlobalTheory.KS.InvField
end
