import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.VeryAmpleCompactQuasiSeparatedAffineCharts
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ThreeTermComplexOfProjectiveCechModel
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCover
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProjByBaseChange
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UnifPreGenericFibreSurjectiveAppTopAndIsIntegral
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CechLBExactAtOfDimLt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CechComplexAcyclicPrimitiveNontrivialAlgClosedStatement

noncomputable section
namespace GlobalTheory.KernelYoneda
open Matrix
variable {A : Type} [CommRing A]

abbrev Coker {a b : ℕ} (D : Matrix (Fin b) (Fin a) A) : Type :=
  (Fin a → A) ⧸ LinearMap.range D.transpose.mulVecLin

def gen {a b : ℕ} (D : Matrix (Fin b) (Fin a) A) (k : Fin a) : Coker D :=
  Submodule.Quotient.mk (Pi.single k 1)

theorem mk_eq_sum {a b : ℕ} (D : Matrix (Fin b) (Fin a) A) (x : Fin a → A) :
    (Submodule.Quotient.mk x : Coker D) = ∑ k, x k • gen D k := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  rw [← Submodule.mkQ_apply, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_smul]; rfl

theorem sum_gen {a b : ℕ} (D : Matrix (Fin b) (Fin a) A) (j : Fin b) :
    ∑ k, D j k • gen D k = 0 := by
  rw [← mk_eq_sum D (D j), Submodule.Quotient.mk_eq_zero]
  exact ⟨Pi.single j 1, by ext k; simp⟩

theorem hom_ext {a b : ℕ} (D : Matrix (Fin b) (Fin a) A) {N : Type} [AddCommGroup N] [Module A N]
    {α β : Coker D →ₗ[A] N} (h : ∀ k, α (gen D k) = β (gen D k)) : α = β := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [mk_eq_sum, map_sum, map_smul, h]

theorem exists_hom {a b : ℕ} (D : Matrix (Fin b) (Fin a) A) {N : Type} [AddCommGroup N] [Module A N]
    (n : Fin a → N) (hn : ∀ j, ∑ k, D j k • n k = 0) :
    ∃ α : Coker D →ₗ[A] N, ∀ k, α (gen D k) = n k := by
  refine ⟨Submodule.liftQ _ (Fintype.linearCombination A n) ?_, fun k => ?_⟩
  · rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, pi_eq_sum_univ' y, map_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul, map_smul]
    have : Fintype.linearCombination A n (D.transpose.mulVecLin (Pi.single j 1)) = 0 := by
      rw [← hn j, Fintype.linearCombination_apply]
      simp
    rw [this, smul_zero]
  · simp [gen, Fintype.linearCombination_apply_single]

open TrivSqZeroExt

section
variable {N : Type} [AddCommGroup N] [Module A N] [Module Aᵐᵒᵖ N] [IsCentralScalar A N]

theorem mulVec_inr_iff {a b : ℕ} (D : Matrix (Fin b) (Fin a) A) (n : Fin a → N) :
    (D.map (algebraMap A (TrivSqZeroExt A N))).mulVec (fun k => inr (n k)) = 0 ↔
      ∀ j, ∑ k, D j k • n k = 0 := by
  have key (j : Fin b) : (D.map (algebraMap A (TrivSqZeroExt A N))).mulVec (fun k => inr (n k)) j =
      inr (∑ k, D j k • n k) := by
    rw [inr_sum]
    change ∑ k, (inl (D j k) * inr (n k) : TrivSqZeroExt A N) = _
    simp only [inl_mul_inr]
  refine funext_iff.trans (forall_congr' fun j => ?_)
  rw [key, Pi.zero_apply, ← inr_zero (R := A) (M := N)]
  exact inr_injective.eq_iff

end

theorem exists_hom_of_rel {a b a' b' : ℕ} (D : Matrix (Fin b) (Fin a) A) (D' : Matrix (Fin b') (Fin a') A)
    (Rel : ∀ (R : Type) [CommRing R] (_ : A →+* R), (Fin a → R) → (Fin a' → R) → Prop)
    (zero : Rel A (RingHom.id A) 0 0)
    (nat : ∀ (R S : Type) [CommRing R] [CommRing S] (g : A →+* R) (h : R →+* S) v w,
      Rel R g v w → Rel S (h.comp g) (h ∘ v) (h ∘ w))
    (ex : ∀ (R : Type) [CommRing R] (g : A →+* R) v, (D.map g).mulVec v = 0 →
      ∃ w, (D'.map g).mulVec w = 0 ∧ Rel R g v w)
    (un : ∀ (R : Type) [CommRing R] (g : A →+* R) v w w', (D'.map g).mulVec w = 0 →
      (D'.map g).mulVec w' = 0 → Rel R g v w → Rel R g v w' → w = w') :
    ∃ α : Coker D' →ₗ[A] Coker D, Rel (TrivSqZeroExt A (Coker D)) (algebraMap _ _)
      (fun k => inr (gen D k)) (fun l => inr (α (gen D' l))) := by
  obtain ⟨w, hw, hr⟩ := ex (TrivSqZeroExt A (Coker D)) (algebraMap _ _) (fun k => inr (gen D k))
    ((mulVec_inr_iff D _).2 (sum_gen D))
  let p : TrivSqZeroExt A (Coker D) →+* A := (fstHom A A (Coker D)).toRingHom
  have hp : p.comp (algebraMap _ _) = RingHom.id A := RingHom.ext fun _ => rfl
  have h₁ := nat _ _ _ p _ _ hr
  rw [hp] at h₁
  have h₂ : p ∘ w = 0 := by
    refine un A (RingHom.id A) 0 _ _ ?_ (Matrix.mulVec_zero _) h₁ zero
    funext j
    have := RingHom.map_mulVec p (D'.map (algebraMap _ _)) w j
    rw [hw, Matrix.map_map, ← RingHom.coe_comp, hp] at this
    exact this.symm.trans (map_zero p)
  have h₃ : w = fun l => inr (w l).snd := funext fun l =>
    TrivSqZeroExt.ext (congrFun h₂ l) rfl
  rw [h₃] at hw hr
  obtain ⟨α, hα⟩ := exists_hom D' _ ((mulVec_inr_iff D' _).1 hw)
  exact ⟨α, by simpa only [hα] using hr⟩

theorem comp_eq_id {a b a' b' : ℕ} (D : Matrix (Fin b) (Fin a) A) (D' : Matrix (Fin b') (Fin a') A)
    (Rel : ∀ (R : Type) [CommRing R] (_ : A →+* R), (Fin a → R) → (Fin a' → R) → Prop)
    (nat : ∀ (R S : Type) [CommRing R] [CommRing S] (g : A →+* R) (h : R →+* S) v w,
      Rel R g v w → Rel S (h.comp g) (h ∘ v) (h ∘ w))
    (un : ∀ (R : Type) [CommRing R] (g : A →+* R) v v' w, (D.map g).mulVec v = 0 →
      (D.map g).mulVec v' = 0 → Rel R g v w → Rel R g v' w → v = v')
    (α : Coker D' →ₗ[A] Coker D) (β : Coker D →ₗ[A] Coker D')
    (hα : Rel (TrivSqZeroExt A (Coker D)) (algebraMap _ _)
      (fun k => inr (gen D k)) (fun l => inr (α (gen D' l))))
    (hβ : Rel (TrivSqZeroExt A (Coker D')) (algebraMap _ _)
      (fun k => inr (β (gen D k))) (fun l => inr (gen D' l))) : α ∘ₗ β = LinearMap.id := by
  let p : TrivSqZeroExt A (Coker D') →+* TrivSqZeroExt A (Coker D) := (TrivSqZeroExt.map α).toRingHom
  have hp : p.comp (algebraMap _ _) = algebraMap _ _ := (TrivSqZeroExt.map α).comp_algebraMap
  have hi (x : Coker D') : p (inr x) = inr (α x) := map_inr α x
  have h₁ := nat _ _ _ p _ _ hβ
  rw [hp] at h₁
  simp only [Function.comp_def, hi] at h₁
  have h₂ := un _ _ _ _ _ ((mulVec_inr_iff D fun k => α (β (gen D k))).2 fun j => by
    simp only [← map_smul, ← map_sum, sum_gen, map_zero]) ((mulVec_inr_iff D _).2 (sum_gen D)) h₁ hα
  exact hom_ext D fun k => inr_injective (congrFun h₂ k)

theorem nonempty_equiv {a b a' b' : ℕ} (D : Matrix (Fin b) (Fin a) A) (D' : Matrix (Fin b') (Fin a') A)
    (Rel : ∀ (R : Type) [CommRing R] (_ : A →+* R), (Fin a → R) → (Fin a' → R) → Prop)
    (zero : Rel A (RingHom.id A) 0 0)
    (nat : ∀ (R S : Type) [CommRing R] [CommRing S] (g : A →+* R) (h : R →+* S) v w,
      Rel R g v w → Rel S (h.comp g) (h ∘ v) (h ∘ w))
    (ex : ∀ (R : Type) [CommRing R] (g : A →+* R) v, (D.map g).mulVec v = 0 →
      ∃ w, (D'.map g).mulVec w = 0 ∧ Rel R g v w)
    (un : ∀ (R : Type) [CommRing R] (g : A →+* R) v w w', (D'.map g).mulVec w = 0 →
      (D'.map g).mulVec w' = 0 → Rel R g v w → Rel R g v w' → w = w')
    (ex' : ∀ (R : Type) [CommRing R] (g : A →+* R) w, (D'.map g).mulVec w = 0 →
      ∃ v, (D.map g).mulVec v = 0 ∧ Rel R g v w)
    (un' : ∀ (R : Type) [CommRing R] (g : A →+* R) v v' w, (D.map g).mulVec v = 0 →
      (D.map g).mulVec v' = 0 → Rel R g v w → Rel R g v' w → v = v') :
    Nonempty (Coker D' ≃ₗ[A] Coker D) := by
  obtain ⟨α, hα⟩ := exists_hom_of_rel D D' Rel zero nat ex un
  obtain ⟨β, hβ⟩ := exists_hom_of_rel D' D (fun R _ g w v => Rel R g v w) zero
    (fun R S _ _ g h w v => nat R S g h v w) ex' (fun R _ g w v v' => un' R g v v' w)
  exact ⟨LinearEquiv.ofLinear α β (comp_eq_id D D' Rel nat un' α β hα hβ)
    (comp_eq_id D' D (fun R _ g w v => Rel R g v w) (fun R S _ _ g h w v => nat R S g h v w)
      (fun R _ g w w' v => un R g v w w') β α hβ hα)⟩

open TensorProduct in

theorem bijOn_basis {P₀ P₁ : Type} [AddCommGroup P₀] [Module A P₀] [AddCommGroup P₁] [Module A P₁]
    {a b : ℕ} (b₀ : Module.Basis (Fin a) A P₀) (b₁ : Module.Basis (Fin b) A P₁) (d : P₀ →ₗ[A] P₁)
    (R : Type) [CommRing R] [Algebra A R] :
    Set.BijOn (fun v : Fin a → R => ∑ k, v k ⊗ₜ[A] b₀ k)
      {v | ((LinearMap.toMatrix b₀ b₁ d).map (algebraMap A R)).mulVec v = 0}
      (LinearMap.ker (d.baseChange R)) := by
  have e : (fun v : Fin a → R => ∑ k, v k ⊗ₜ[A] b₀ k) =
      (Algebra.TensorProduct.basis R b₀).equivFun.symm := by
    funext v
    simp [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
  rw [e]
  refine (Algebra.TensorProduct.basis R b₀).equivFun.symm.toEquiv.bijOn fun v => ?_
  have h := LinearMap.toMatrix_mulVec_repr (Algebra.TensorProduct.basis R b₀)
    (Algebra.TensorProduct.basis R b₁) (d.baseChange R) ((Algebra.TensorProduct.basis R b₀).equivFun.symm v)
  rw [LinearMap.toMatrix_baseChange, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply,
    ← Module.Basis.equivFun_apply] at h
  change d.baseChange R ((Algebra.TensorProduct.basis R b₀).equivFun.symm v) = 0 ↔ _
  rw [Set.mem_setOf_eq, h, map_eq_zero_iff _ (LinearEquiv.injective _)]

theorem nonempty_dual_equiv {P₀ P₁ : Type} [AddCommGroup P₀] [Module A P₀] [AddCommGroup P₁] [Module A P₁]
    {a b : ℕ} (b₀ : Module.Basis (Fin a) A P₀) (b₁ : Module.Basis (Fin b) A P₁) (d : P₀ →ₗ[A] P₁) :
    Nonempty ((Module.Dual A P₀ ⧸ LinearMap.range d.dualMap) ≃ₗ[A] Coker (LinearMap.toMatrix b₀ b₁ d)) := by
  have key (ψ : Module.Dual A P₁) : b₀.dualBasis.equivFun (d.dualMap ψ) =
      (LinearMap.toMatrix b₀ b₁ d).transpose.mulVecLin (b₁.dualBasis.equivFun ψ) := by
    rw [← LinearMap.toMatrix_transpose]
    exact (LinearMap.toMatrix_mulVec_repr b₁.dualBasis b₀.dualBasis d.dualMap ψ).symm
  refine ⟨Submodule.Quotient.equiv _ _ b₀.dualBasis.equivFun ?_⟩
  ext x
  constructor
  · rintro ⟨_, ⟨ψ, rfl⟩, rfl⟩
    exact ⟨_, (key ψ).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨ψ, rfl⟩ := b₁.dualBasis.equivFun.surjective y
    exact ⟨_, ⟨ψ, rfl⟩, key ψ⟩

end GlobalTheory.KernelYoneda

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw.SecKernel
open GlobalTheory.KernelYoneda TensorProduct
variable {A : Type} [CommRing A] {X : Scheme.{0}}

def loc {R : Type} [CommRing R] {X' : Scheme.{0}} (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R))
    {a : ℕ} (V : X.Opens) (u : Fin a → Γ(X, V)) (v : Fin a → R) : Γ(X', π ⁻¹ᵁ V) :=
  ∑ k, cst f' (π ⁻¹ᵁ V) (v k) * (π.app V).hom (u k)

def Computes (f : X ⟶ Spec (CommRingCat.of A)) (M : LB X) {a b : ℕ} (D : Matrix (Fin b) (Fin a) A)
    {I : Type} (W : I → X.Opens) (ch : I → M.ι) (le : ∀ i, W i ≤ M.U (ch i))
    (u : Fin a → ∀ i, Γ(X, W i)) : Prop :=
  ∀ (R : Type) [CommRing R] (g : A →+* R) (X' : Scheme.{0}) (π : X' ⟶ X)
    (f' : X' ⟶ Spec (CommRingCat.of R)), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) →
    ∃ E : {v : Fin a → R // (D.map g).mulVec v = 0} ≃ LB.Sec (M.pull π),
      ∀ v i, rs X' (le_pull M π (le i)) ((E v).f (fun _ => ch i)) = loc π f' (W i) (fun k => u k i) v.1

theorem rs_loc {R : Type} [CommRing R] {X' : Scheme.{0}} (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R))
    {a : ℕ} {V W : X.Opens} (h : V ≤ W) (u : Fin a → Γ(X, W)) (v : Fin a → R) :
    rs X' (π.preimage_mono h) (loc π f' W u v) = loc π f' V (fun k => rs X h (u k)) v := by
  rw [loc, map_sum]
  refine Finset.sum_congr rfl fun k _ => (map_mul _ _ _).trans (congrArg₂ (· * ·) (rs_cst f' _ _) ?_)
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
  exact (GlobalTheory.LB.resG_appLE π _ _ _).trans (GlobalTheory.LB.appLE_resG π _ _ _).symm

theorem appLE_loc {R S : Type} [CommRing R] [CommRing S] {X' X'' : Scheme.{0}} (π : X' ⟶ X)
    (f' : X' ⟶ Spec (CommRingCat.of R)) (π' : X'' ⟶ X) (f'' : X'' ⟶ Spec (CommRingCat.of S))
    (ψ : X'' ⟶ X') (h : R →+* S) (e₁ : ψ ≫ π = π')
    (e₂ : ψ ≫ f' = f'' ≫ Spec.map (CommRingCat.ofHom h))
    {a : ℕ} (V : X.Opens) (e : π' ⁻¹ᵁ V ≤ ψ ⁻¹ᵁ π ⁻¹ᵁ V) (u : Fin a → Γ(X, V)) (v : Fin a → R) :
    (ψ.appLE _ _ e).hom (loc π f' V u v) = loc π' f'' V u (h ∘ v) := by
  subst e₁
  rw [loc, map_sum]
  refine Finset.sum_congr rfl fun k _ => (map_mul _ _ _).trans (congrArg₂ (· * ·) (appLE_cst e₂ e _) ?_)
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
  exact congrArg (fun q => q.hom (u k)) (Scheme.Hom.appLE_comp_appLE ψ π V _ _ le_rfl e)

variable {f : X ⟶ Spec (CommRingCat.of A)} {M : LB X}

theorem computes_perf (P : Perf f M) : Computes f M P.D₀ P.W P.ch P.le P.u := P.sec

theorem Computes.refine {a b : ℕ} {D : Matrix (Fin b) (Fin a) A}
    {I : Type} {W : I → X.Opens} {ch : I → M.ι} {le : ∀ i, W i ≤ M.U (ch i)}
    {u : Fin a → ∀ i, Γ(X, W i)} (h : Computes f M D W ch le u) {J : Type} (V : J → X.Opens)
    (τ : J → I) (hV : ∀ j, V j ≤ W (τ j)) :
    Computes f M D V (fun j => ch (τ j)) (fun j => (hV j).trans (le _))
      (fun k j => rs X (hV j) (u k (τ j))) := by
  intro R _ g X' π f' H
  obtain ⟨E, hE⟩ := h R g X' π f' H
  refine ⟨E, fun v j => ?_⟩
  rw [← rs_loc π f' (hV j), ← hE, rs_rs]

theorem Computes.nonempty_equiv {a b a' b' : ℕ} {D : Matrix (Fin b) (Fin a) A}
    {D' : Matrix (Fin b') (Fin a') A}
    {I : Type} {W : I → X.Opens} {ch : I → M.ι} {le : ∀ i, W i ≤ M.U (ch i)}
    {u : Fin a → ∀ i, Γ(X, W i)} {u' : Fin a' → ∀ i, Γ(X, W i)} (hc : ∀ x, ∃ i, x ∈ W i)
    (h : Computes f M D W ch le u) (h' : Computes f M D' W ch le u') :
    Nonempty (Coker D' ≃ₗ[A] Coker D) := by
  let Rel : ∀ (R : Type) [CommRing R] (_ : A →+* R), (Fin a → R) → (Fin a' → R) → Prop :=
    fun R _ g v w => ∀ i,
      loc (pullback.fst f (Spec.map (CommRingCat.ofHom g))) (pullback.snd _ _) (W i) (fun k => u k i) v =
      loc (pullback.fst f (Spec.map (CommRingCat.ofHom g))) (pullback.snd _ _) (W i) (fun k => u' k i) w
  have key (R : Type) [CommRing R] (g : A →+* R) :
      ∃ e : {v : Fin a → R // (D.map g).mulVec v = 0} ≃ {v : Fin a' → R // (D'.map g).mulVec v = 0},
        ∀ v w, Rel R g v.1 w.1 ↔ e v = w := by
    obtain ⟨E, hE⟩ := h R g _ _ _ (IsPullback.of_hasPullback _ _)
    obtain ⟨E', hE'⟩ := h' R g _ _ _ (IsPullback.of_hasPullback _ _)
    refine ⟨E.trans E'.symm, fun v w => ?_⟩
    rw [Equiv.trans_apply, Equiv.symm_apply_eq]
    refine ⟨fun hr => Seesaw.sec_ext _ _ _ _ (fun i => le_pull M _ (le i)) (fun y => hc _) fun i => ?_,
      fun hr i => ?_⟩
    · rw [hE, hE', hr i]
    · rw [← hE, ← hE', hr]
  refine KernelYoneda.nonempty_equiv D D' Rel (fun i => by simp [loc]) ?_ ?_ ?_ ?_ ?_
  · intro R S _ _ g p v w hr i
    have hs : Spec.map (CommRingCat.ofHom (p.comp g)) =
        Spec.map (CommRingCat.ofHom p) ≫ Spec.map (CommRingCat.ofHom g) := by
      rw [← Spec.map_comp]; rfl
    let ψ : pullback f (Spec.map (CommRingCat.ofHom (p.comp g))) ⟶ pullback f (Spec.map (CommRingCat.ofHom g)) :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom p))
        (by rw [pullback.condition, Category.assoc, hs])
    have e₁ : ψ ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
    have e₂ : ψ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom p) :=
      pullback.lift_snd _ _ _
    have e : pullback.fst f (Spec.map (CommRingCat.ofHom (p.comp g))) ⁻¹ᵁ W i ≤
        ψ ⁻¹ᵁ pullback.fst f (Spec.map (CommRingCat.ofHom g)) ⁻¹ᵁ W i := by
      rw [← Scheme.Hom.comp_preimage, e₁]
    rw [← appLE_loc _ _ _ _ ψ p e₁ e₂ _ e, ← appLE_loc _ _ _ _ ψ p e₁ e₂ _ e, hr i]
  · intro R _ g v hv
    obtain ⟨e, he⟩ := key R g
    exact ⟨_, (e ⟨v, hv⟩).2, (he ⟨v, hv⟩ _).2 rfl⟩
  · intro R _ g v w w' hw hw' h₁ h₂
    obtain ⟨e, he⟩ := key R g
    have h₃ := (he (e.symm ⟨w, hw⟩) ⟨w, hw⟩).2 (e.apply_symm_apply _)
    exact congrArg Subtype.val ((e.apply_symm_apply _).symm.trans ((he (e.symm ⟨w, hw⟩) ⟨w', hw'⟩).1
      fun i => (h₃ i).trans ((h₁ i).symm.trans (h₂ i))))
  · intro R _ g w hw
    obtain ⟨e, he⟩ := key R g
    exact ⟨_, (e.symm ⟨w, hw⟩).2, (he _ ⟨w, hw⟩).2 (e.apply_symm_apply _)⟩
  · intro R _ g v v' w hv hv' h₁ h₂
    obtain ⟨e, he⟩ := key R g
    have h₃ := (he ⟨v, hv⟩ _).2 rfl
    exact congrArg Subtype.val (e.injective ((he ⟨v', hv'⟩ _).1
      fun i => (h₂ i).trans ((h₁ i).symm.trans (h₃ i))).symm)

open PerfOfModel in

theorem computes_of_model {κ : Type} [LinearOrder κ] [Fintype κ] {D : κ → X.Opens}
    {K : CochainComplex (ModuleCat.{0} A) ℕ} (φ : K ⟶ cechLB f M D) (hM : M.IsLB) (hc : ⨆ i, D i = ⊤)
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i))
    (hq : ∀ (R : Type) [CommRing R] [Algebra A R], QuasiIso
      (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap A R)).mapHomologicalComplex _).map φ))
    {a b : ℕ} (b₀ : Module.Basis (Fin a) A (K.X 0)) (b₁ : Module.Basis (Fin b) A (K.X 1)) :
    Computes f M (LinearMap.toMatrix b₀ b₁ (K.d 0 1).hom)
      (fun p : κ × M.ι => (⨅ i ∈ ({p.1} : Finset κ), D i) ⊓ M.U p.2) (fun p => p.2)
      (fun _ => inf_le_right)
      (fun k p => SecOnR.coord (f := f) ((φ.f 0).hom (b₀ k) ⟨{p.1}, Finset.card_singleton _⟩) p.2) := by
  intro R _ g Y' π f' H
  letI := g.toAlgebra
  have B := ((termMap_bijOn hM H hD).comp
    (bijOn_ker_and_exact_of_quasiIso_baseChange A R K _ φ (hq R)).1).comp
      (bijOn_basis b₀ b₁ (K.d 0 1).hom R)
  let S := CechOne.secKerEquiv (M.pull π) f' (iSup_preimage π hc)
  refine ⟨(B.equiv _).trans S.symm.toEquiv, fun v p => ?_⟩
  have hv : (S (S.symm (B.equiv _ v))).1 =
      termMap M D H.w 0 (∑ k, v.1 k ⊗ₜ[A] (φ.f 0).hom (b₀ k)) := by
    rw [S.apply_symm_apply]
    change termMap M D H.w 0 ((φ.f 0).hom.baseChange R (∑ k, v.1 k ⊗ₜ[A] b₀ k)) = _
    rw [map_sum ((φ.f 0).hom.baseChange R)]
    rfl
  have hle : π ⁻¹ᵁ ((⨅ i ∈ ({p.1} : Finset κ), D i) ⊓ M.U p.2) ≤
      (⨅ i ∈ ({p.1} : Finset κ), π ⁻¹ᵁ D i) ⊓ (M.pull π).U fun _ => p.2 :=
    le_inf ((π.preimage_mono inf_le_left).trans (preimage_biInf D π _).le)
      (le_pull M π inf_le_right)
  refine Eq.trans ?_ (coord_termMap_sum H.w v.1 (fun k => (φ.f 0).hom (b₀ k))
    ⟨{p.1}, Finset.card_singleton _⟩ p.2 hle)
  rw [← hv, CechOne.secKerEquiv_val]
  exact (rs_rs inf_le_right hle _).symm

theorem nonempty_equiv_of_model {κ : Type} [LinearOrder κ] [Fintype κ] {D : κ → X.Opens}
    {K : CochainComplex (ModuleCat.{0} A) ℕ} (φ : K ⟶ cechLB f M D) (hM : M.IsLB) (hc : ⨆ i, D i = ⊤)
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i))
    (hq : ∀ (R : Type) [CommRing R] [Algebra A R], QuasiIso
      (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap A R)).mapHomologicalComplex _).map φ))
    (hK : ∀ i, Module.Free A (K.X i) ∧ Module.Finite A (K.X i)) (P : Perf f M) :
    Nonempty ((Module.Dual A (K.X 0) ⧸ LinearMap.range (K.d 0 1).hom.dualMap) ≃ₗ[A] Coker P.D₀) := by
  haveI := fun p => (hK p).1
  haveI := fun p => (hK p).2
  let b₀ := (Module.Free.chooseBasis A (K.X 0)).reindex (Fintype.equivFin _)
  let b₁ := (Module.Free.chooseBasis A (K.X 1)).reindex (Fintype.equivFin _)
  let V : P.I × κ → X.Opens := fun q => P.W q.1 ⊓ ((⨅ i ∈ ({q.2} : Finset κ), D i) ⊓ M.U (P.ch q.1))
  have h₁ := (computes_perf P).refine V Prod.fst
    fun _ => inf_le_left
  have h₂ := (computes_of_model φ hM hc hD hq b₀ b₁).refine V (fun q => (q.2, P.ch q.1))
    fun _ => inf_le_right
  obtain ⟨e₁⟩ := nonempty_dual_equiv b₀ b₁ (K.d 0 1).hom
  refine (Computes.nonempty_equiv (fun x => ?_) h₁ h₂).map e₁.trans
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ x))
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (P.cover.ge (Set.mem_univ x))
    refine ⟨(j, i), hj, ?_, P.le j hj⟩
    rw [Finset.iInf_singleton]
    exact hi

end GlobalTheory.AbLaw.SecKernel

namespace GlobalTheory.AbLaw

theorem exists_free_complex_of_primitive : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ g : ℕ, SmoothOfRelativeDimension g B.hom → ∀ F : LB B.left, F.IsLB → (∃ u : LB.Gen (abelian₂ B F), u.IsGen) → ∀ P : Perf B.hom F, ∃ C : CochainComplex (ModuleCat.{0} A) ℕ, (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i))  ∧ (∃ n, ∀ i, n < i → IsZero (C.X i)) ∧ Nonempty ((Module.Dual A (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A] ((Fin P.a → A) ⧸ LinearMap.range P.D₀.transpose.mulVecLin)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (φ : A →+* K) (X' : Scheme.{0}) (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom φ)) → ∀ i, (g < i ∨ ¬ Triv (F.pull π)) → (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i := by
  intro A _ _ _ B _ _ hB hP g hg F hF hu P
  obtain ⟨u, hu⟩ := hu
  have := hB.smooth
  have := hB.proper
  obtain ⟨H, hH, m, s, hs⟩ := id hP
  have hD := (VeryAmpleCharts.compact_quasiSeparated_isAffineOpen A _ B.hom H m s hH hs).2.2
  have hD₁ := fun i => (hs.2 i).1
  obtain ⟨C, ψ, h0, hfin, -, hproj, -, -, hq⟩ := exists_finite_projective_complex_quasiIso.{0, 0}
    (cechLB B.hom F fun i => nonzeroLocus (s i)) (Fintype.card (Fin (m + 1)))
    (fun p hp => isZero_cechLB_X _ _ _ hp.le) (flat_cechLB_X B.hom hF hD)
    (cechLB_homology_finite_of_affine_cover A _ B.hom F _ _ hF inferInstance hP hD₁ hs.1)
  have hC : ∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i) := fun i => by
    have := hfin i
    have := hproj i
    exact ⟨Module.free_of_flat_of_isLocalRing, hfin i⟩
  refine ⟨C, hC, ⟨_, h0⟩, SecKernel.nonempty_equiv_of_model ψ hF hs.1 hD hq hC P, ?_⟩
  intro K _ _ φ X' π f' hX i hi
  let t := Spec.map (CommRingCat.ofHom φ)
  let B' := (Over.pullback t).obj B
  have : IsCommMonObj B' := Functor.isCommMonObj_obj
  have hB' : IsAbelianScheme B' := Out.TLinPf.isAb_pullback t B hB
  have sq : IsPullback (pullback.fst B.hom t) B'.hom B.hom t := IsPullback.of_hasPullback _ _
  have hP' : IsProjBy B'.hom := isProjBy_baseChange _ _ φ _ _ _ _ _ sq hP
  have hF' := LB.isLB_pull hF (pullback.fst B.hom t)
  have ha := fun j => isAffineOpen_preimage_of_isPullback sq (hD₁ j)
  have hc := PerfOfModel.iSup_preimage (pullback.fst B.hom t) hs.1
  have hq' : QuasiIso (((ModuleCat.extendScalars φ).mapHomologicalComplex _).map ψ) :=
    letI := φ.toAlgebra
    hq K
  refine (exactAt_iff_of_quasiIsoAt
    (((ModuleCat.extendScalars φ).mapHomologicalComplex _).map ψ ≫ (cechLBBaseChangeIso hF sq hD).hom) i).2 ?_
  rcases hi with hi | hi
  · have := isIntegral_left_of_isAbelianScheme_field B' hB'
    have := hB'.proper
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} (n := g)
    exact cechLB_exactAt_of_dim_lt K B'.left B'.hom g _
      (MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) sq hg) hP' inferInstance hF' _ _ ha hc i hi
  · obtain ⟨U, ⟨c⟩⟩ := GtBaseChange.exists_lamChart t B F
    exact GlobalTheory.T.cechComplex_acyclic_primitive_nontrivial_algClosed K B' hB' hP' _ hF' ⟨_, GtBaseChange.genPull_isGen c hu⟩
      (fun h => hi (CubeOpen.triv_comp (hX.isoIsPullback _ _ sq).hom (hX.isoIsPullback_hom_fst _ _ sq) h))
      _ _ ha hc i

end GlobalTheory.AbLaw
