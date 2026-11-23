import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatTrans

section Pull

variable {X Y Z : Scheme.{0}}

theorem pbT_pbT (T : Z ⟶ Y) (S : Y ⟶ X) {O₀ : X.Opens} {O₁ : Y.Opens} {O₂ : Z.Opens} (h₁ : O₁ ≤ S ⁻¹ᵁ O₀)
    (h₂ : O₂ ≤ T ⁻¹ᵁ O₁) (s : Γ(X, O₀)) : pbT T (pbT S s O₁) O₂ = pbT (T ≫ S) s O₂ := by
  rw [GlobalTheory.KS.pbT_of_le S h₁, GlobalTheory.KS.pbT_of_le T h₂, GlobalTheory.KS.pbT_of_le (T ≫ S) (h₂.trans (T.preimage_mono h₁))]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_comp_appLE T S O₀ O₁ O₂ h₁ h₂)

theorem pbT_id {O₀ O : Z.Opens} (h : O ≤ O₀) (s : Γ(Z, O₀)) : pbT (𝟙 Z) s O = rsT s O := by
  rw [GlobalTheory.KS.pbT_of_le (𝟙 Z) h, GlobalTheory.KS.rsT_of_le h]
  simp [Scheme.Hom.appLE]
  rfl

theorem pbT_pow (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) (s : Γ(Y, O₀)) (k : ℕ) :
    pbT f (s ^ k) O = pbT f s O ^ k := by
  rw [GlobalTheory.KS.pbT_of_le f h, GlobalTheory.KS.pbT_of_le f h, map_pow]

end Pull

def conjF {Z : Scheme.{0}} (T S : Z ⟶ Z) (d : Fld Z) : Fld Z :=
  fun O f => pbT T (d (S ⁻¹ᵁ O) (pbT S f (S ⁻¹ᵁ O))) O

section Tr

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G]

def tr (x : 𝟙_ (Over (Sp R)) ⟶ G) : G.left ⟶ G.left := (𝟙 G * (toUnit G ≫ x)).left

theorem tr_over (x : 𝟙_ (Over (Sp R)) ⟶ G) : (𝟙 G * (toUnit G ≫ x)) ≫ (𝟙 G * (toUnit G ≫ x⁻¹)) = 𝟙 G := by
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique ((𝟙 G * (toUnit G ≫ x)) ≫ toUnit G) (toUnit G),
    _root_.mul_assoc, ← MonObj.comp_mul, _root_.mul_inv_cancel, MonObj.comp_one, _root_.mul_one]

theorem tr_tr_inv (x : 𝟙_ (Over (Sp R)) ⟶ G) : tr G x ≫ tr G x⁻¹ = 𝟙 _ := by
  rw [tr, tr, ← Over.comp_left, tr_over]; rfl

theorem tr_inv_tr (x : 𝟙_ (Over (Sp R)) ⟶ G) : tr G x⁻¹ ≫ tr G x = 𝟙 _ := by
  have := tr_tr_inv G x⁻¹
  rwa [inv_inv] at this

theorem tr_hom (x : 𝟙_ (Over (Sp R)) ⟶ G) : tr G x ≫ G.hom = G.hom := by
  rw [tr]; exact (Over.w _)

end Tr

section Field

variable {Z : Scheme.{0}}

theorem rsT_natCast {O₀ O : Z.Opens} (h : O ≤ O₀) (m : ℕ) : rsT (m : Γ(Z, O₀)) O = m := by
  rw [GlobalTheory.KS.rsT_of_le h, map_natCast]

theorem rsT_ofNat {O₀ O : Z.Opens} (h : O ≤ O₀) (m : ℕ) [m.AtLeastTwo] :
    rsT (OfNat.ofNat m : Γ(Z, O₀)) O = OfNat.ofNat m := by
  rw [GlobalTheory.KS.rsT_of_le h, map_ofNat]

theorem rsT_pow {O₀ O : Z.Opens} (h : O ≤ O₀) (s : Γ(Z, O₀)) (m : ℕ) : rsT (s ^ m) O = rsT s O ^ m := by
  rw [GlobalTheory.KS.rsT_of_le h, GlobalTheory.KS.rsT_of_le h, map_pow]

theorem op_rsT {R : Type} [CommRing R] (G : Over (Sp R)) {n : ℕ} (dd : Fin n → Fld G.left)
    (hdd : ∀ a, IsField ⊤ (dd a)) (Θ : Matrix (Fin n) (Fin n) R) (u : Fin n → R) {W : G.left.Opens} (d : Fld G.left)
    (hd : IsField W d) (p p' : Γ(G.left, W)) (k : ℕ) {O O' : G.left.Opens} (h : O' ≤ O) (hO : O ≤ W)
    (f : Γ(G.left, O)) : op G dd Θ u d p p' k O' (rsT f O') = rsT (op G dd Θ u d p p' k O f) O' := by
  have e1 : ∀ a (g : Γ(G.left, O)), dd a O' (rsT g O') = rsT (dd a O g) O' := fun a g => by
    rw [GlobalTheory.KS.rsT_of_le h, GlobalTheory.KS.rsT_of_le h]; exact (hdd a).2.2 O O' h le_top g
  have e2 : ∀ g : Γ(G.left, O), d O' (rsT g O') = rsT (d O g) O' := fun g => by
    rw [GlobalTheory.KS.rsT_of_le h, GlobalTheory.KS.rsT_of_le h]; exact hd.2.2 O O' h hO g
  simp only [op, GlobalTheory.KS.rsT_add, GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_mul, GlobalTheory.KS.rsT_sum, e1, e2,
    GlobalTheory.KS.rsT_constFn _ h, GlobalTheory.KS.rsT_rsT hO h, rsT_natCast h, rsT_ofNat h, rsT_pow h]

end Field

section Conj

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]

theorem isLift_conjF (D : R → R) {T S : G.left ⟶ G.left} (hTS : T ≫ S = 𝟙 _) (hST : S ≫ T = 𝟙 _)
    (hT : T ≫ G.hom = G.hom) (hS : S ≫ G.hom = G.hom) {W : G.left.Opens} {d : Fld G.left} (hl : IsLift G D W d) :
    IsLift G D (T ⁻¹ᵁ W) (conjF T S d) := by
  have hpre : ∀ U : G.left.Opens, S ⁻¹ᵁ (T ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hST]; rfl
  have hpre' : ∀ U : G.left.Opens, T ⁻¹ᵁ (S ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hTS]; rfl
  have hSO : ∀ O, O ≤ T ⁻¹ᵁ W → S ⁻¹ᵁ O ≤ W := fun O hO => (S.preimage_mono hO).trans (hpre W).le
  have back : ∀ (O : G.left.Opens) (f : Γ(G.left, O)), pbT T (pbT S f (S ⁻¹ᵁ O)) O = f := fun O f => by
    rw [pbT_pbT T S le_rfl (hpre' O).ge, hTS, pbT_id le_rfl, GlobalTheory.KS.rsT_self]
  refine ⟨⟨fun O hO f f' => ?_, fun O hO f f' => ?_, fun O O' hle hO f => ?_⟩, fun O hO r => ?_⟩
  · simp only [conjF]
    rw [GlobalTheory.KS.pbT_add, hl.1.1 _ (hSO O hO), GlobalTheory.KS.pbT_add]
  · simp only [conjF]
    rw [GlobalTheory.KS.pbT_mul, hl.1.2.1 _ (hSO O hO), GlobalTheory.KS.pbT_add, GlobalTheory.KS.pbT_mul, GlobalTheory.KS.pbT_mul, back, back]
  · simp only [conjF]
    have hS' : S ⁻¹ᵁ O' ≤ S ⁻¹ᵁ O := S.preimage_mono hle
    rw [← GlobalTheory.KS.rsT_of_le hle, ← GlobalTheory.KS.rsT_of_le hle, GlobalTheory.KS.pbT_rsT S hle le_rfl,
      ← GlobalTheory.KS.rsT_pbT S le_rfl hS', GlobalTheory.KS.rsT_of_le hS', hl.1.2.2 _ _ hS' (hSO O hO), ← GlobalTheory.KS.rsT_of_le hS',
      GlobalTheory.KS.pbT_rsT T hS' (hpre' O').ge, GlobalTheory.KS.rsT_pbT T (hpre' O).ge hle]
  · simp only [conjF]
    rw [GlobalTheory.KS.pbT_constFn _ S le_rfl, hS, hl.2 _ (hSO O hO), GlobalTheory.KS.pbT_constFn _ T (hpre' O).ge, hT]

end Conj

section OpConj

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]

theorem pbT_natCast {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) (m : ℕ) :
    pbT f (m : Γ(Y, O₀)) O = m := by
  rw [GlobalTheory.KS.pbT_of_le f h, map_natCast]

theorem pbT_ofNat {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) (m : ℕ)
    [m.AtLeastTwo] : pbT f (OfNat.ofNat m : Γ(Y, O₀)) O = OfNat.ofNat m := by
  rw [GlobalTheory.KS.pbT_of_le f h, map_ofNat]

theorem op_conjF {n : ℕ} (dd : Fin n → Fld G.left) {T S : G.left ⟶ G.left} (hTS : T ≫ S = 𝟙 _) (hST : S ≫ T = 𝟙 _)
    (hT : T ≫ G.hom = G.hom)
    (hdd : ∀ a (O O' : G.left.Opens), O' ≤ T ⁻¹ᵁ O → ∀ f : Γ(G.left, O), dd a O' (pbT T f O') = pbT T (dd a O f) O')
    (Θ : Matrix (Fin n) (Fin n) R) (u : Fin n → R) (d : Fld G.left) {W : G.left.Opens} (p p' : Γ(G.left, W)) (k : ℕ)
    {O : G.left.Opens} (hO : O ≤ T ⁻¹ᵁ W) (f : Γ(G.left, O)) :
    op G dd Θ u (conjF T S d) (pbT T p (T ⁻¹ᵁ W)) (pbT T p' (T ⁻¹ᵁ W)) k O f =
      pbT T (op G dd Θ u d p p' k (S ⁻¹ᵁ O) (pbT S f (S ⁻¹ᵁ O))) O := by
  have hpre : ∀ U : G.left.Opens, S ⁻¹ᵁ (T ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hST]; rfl
  have hpre' : ∀ U : G.left.Opens, T ⁻¹ᵁ (S ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hTS]; rfl
  have hOO : O ≤ T ⁻¹ᵁ (S ⁻¹ᵁ O) := (hpre' O).ge
  have hSO : S ⁻¹ᵁ O ≤ W := (S.preimage_mono hO).trans (hpre W).le
  have back : pbT T (pbT S f (S ⁻¹ᵁ O)) O = f := by
    rw [pbT_pbT T S le_rfl hOO, hTS, pbT_id le_rfl, GlobalTheory.KS.rsT_self]
  have e : ∀ a (X : Γ(G.left, S ⁻¹ᵁ O)), pbT T (dd a (S ⁻¹ᵁ O) X) O = dd a O (pbT T X O) :=
    fun a X => (hdd a _ _ hOO X).symm
  have ep : ∀ q : Γ(G.left, W), pbT T (rsT q (S ⁻¹ᵁ O)) O = rsT (pbT T q (T ⁻¹ᵁ W)) O := fun q => by
    rw [GlobalTheory.KS.pbT_rsT T hSO hOO, GlobalTheory.KS.rsT_pbT T le_rfl hO]
  simp only [op, conjF, GlobalTheory.KS.pbT_add, GlobalTheory.KS.pbT_sub, GlobalTheory.KS.pbT_mul, GlobalTheory.KS.pbT_sum, e, ep, back,
    GlobalTheory.KS.pbT_constFn _ T hOO, hT, pbT_natCast T hOO, pbT_ofNat T hOO, pbT_pow T hOO]

end OpConj

section Ray

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem tr_q (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) : tr Y.H x ≫ Y.q.left = Y.q.left ≫ tr Q.P.A (x ≫ Y.q) := by
  have := Y.q_linear.isMonHom
  have e : (𝟙 Y.H * (toUnit Y.H ≫ x)) ≫ Y.q = Y.q ≫ (𝟙 Q.P.A * (toUnit Q.P.A ≫ x ≫ Y.q)) := by
    rw [MonObj.mul_comp, MonObj.comp_mul, Category.id_comp, Category.comp_id, ← Category.assoc, ← Category.assoc,
      toUnit_unique (Y.q ≫ toUnit Q.P.A) (toUnit Y.H), Category.assoc]
  exact congrArg CommaMorphism.left e

theorem preimage_tr_q (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (V : Q.P.A.left.Opens) :
    tr Y.H x ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V) = Y.q.left ⁻¹ᵁ (tr Q.P.A (x ≫ Y.q) ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, tr_q, Scheme.Hom.comp_preimage]

end Ray

end GlobalTheory.HeatTrans
