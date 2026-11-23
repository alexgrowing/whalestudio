import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiIsEven
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PolTensEven

open TopologicalSpace GlobalTheory.TensEven

section Gen

variable {X X' Y Y₀ : Scheme.{0}} {M : LB X} {M' : LB X'} {P : Type} [Fintype P] {pr : P → (X' ⟶ X)} {εp : P → ℤ}
  {K : Type} [Fintype K] {Q : Type} [Fintype Q] {P₂ : Type} [Fintype P₂]

def wG (φ' : K → (Y ⟶ X')) {φ : Q → (Y₀ ⟶ X)} (ρ : P₂ → (Y ⟶ Y₀)) (I : (Y ⟶ X) → M.ι) (jM : K → M'.ι) : Y.Opens :=
  LB.wchart (LB.LinComb M pr εp) φ' (fun a i => I (φ' a ≫ pr i)) ⊓ LB.wchart M' φ' jM ⊓
    LB.wchart M (fun q : P₂ × Q => ρ q.1 ≫ φ q.2) (fun q => I (ρ q.1 ≫ φ q.2))

theorem chart_leG {φ : Q → (Y₀ ⟶ X)} (ρ : P₂ → (Y ⟶ Y₀)) (I : (Y ⟶ X) → M.ι) (p : P₂) :
    LB.wchart M (fun q : P₂ × Q => ρ q.1 ≫ φ q.2) (fun q => I (ρ q.1 ≫ φ q.2)) ≤
      ρ p ⁻¹ᵁ LB.wchart M φ (fun k => I (ρ p ≫ φ k)) := fun _ hy =>
  Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (p, k)

def ratioG (w : LB.Iso M' (LB.LinComb M pr εp)) {φ' : K → (Y ⟶ X')} {ε : K → ℤ} {φ : Q → (Y₀ ⟶ X)} {δ : Q → ℤ}
    (ρ : P₂ → (Y ⟶ Y₀)) (ν : P₂ → ℤ) (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : LB.Gen (LB.LinComb M φ δ))
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (I : (Y ⟶ X) → M.ι) (jM : K → M'.ι) : (Z.presheaf.stalk z)ˣ :=
  (∏ a, bwE w (r ≫ φ' a) z (fun i => I (φ' a ≫ pr i)) (jM a) ^ ε a) * gm r z (LB.wchart M' φ' jM) (t'.s jM) *
    (∏ p, gm (r ≫ ρ p) z (LB.wchart M φ (fun k => I (ρ p ≫ φ k))) (t.s (fun k => I (ρ p ≫ φ k))) ^ ν p)⁻¹

theorem exists_ratioG (w : LB.Iso M' (LB.LinComb M pr εp)) {φ' : K → (Y ⟶ X')} {ε : K → ℤ} {φ : Q → (Y₀ ⟶ X)}
    {δ : Q → ℤ} (ρ : P₂ → (Y ⟶ Y₀)) (ν : P₂ → ℤ) (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : LB.Gen (LB.LinComb M φ δ))
    (I : (Y ⟶ X) → M.ι) (jM : K → M'.ι) :
    ∃ u : Γ(Y, wG (pr := pr) (εp := εp) φ' (φ := φ) ρ I jM)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
      r z ∈ wG (pr := pr) (εp := εp) φ' (φ := φ) ρ I jM → gm r z _ u = ratioG w ρ ν t' t r z I jM := by
  refine ⟨@id (Γ(Y, wG (pr := pr) (εp := εp) φ' (φ := φ) ρ I jM)ˣ)
      (res inf_le_left ((LB.linCombIso w φ' ε).s ((fun a i => I (φ' a ≫ pr i)), jM)) *
        res (inf_le_left.trans inf_le_right) (t'.s jM) *
      (∏ p, res (inf_le_right.trans (chart_leG ρ I p)) (pullU (ρ p) _ (t.s (fun k => I (ρ p ≫ φ k)))) ^ ν p)⁻¹),
    fun Z r z hz => ?_⟩
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_res r z _ hz _).trans (gm_linCombIsoE w φ' ε r z _ jM hz.1)) (gm_res r z _ hz _))) ((map_inv _ _).trans
      (congrArg (·⁻¹) ((map_prod _ _ _).trans (Finset.prod_congr rfl fun p _ => ?_)))))
  exact (map_zpow _ _ _).trans (congrArg (· ^ ν p)
    ((gm_res r z _ hz _).trans (gm_pull r (ρ p) z _ (chart_leG ρ I p hz.2) _)))

end Gen

section Gen2

variable {X X' Y Y₀ : Scheme.{0}} {M : LB X} {M' : LB X'} {P : Type} [Fintype P] {pr : P → (X' ⟶ X)} {εp : P → ℤ}
  {K : Type} [Fintype K] {Q : Type} [Fintype Q] {P₂ : Type} [Fintype P₂]

theorem ratioG_trans (w : LB.Iso M' (LB.LinComb M pr εp)) (hw : w.IsGen) {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    {φ : Q → (Y₀ ⟶ X)} {δ : Q → ℤ} {ρ : P₂ → (Y ⟶ Y₀)} {ν : P₂ → ℤ}
    (hF : FormEq (fun q : K × P => φ' q.1 ≫ pr q.2) (fun q => ε q.1 * εp q.2) (fun q : P₂ × Q => ρ q.1 ≫ φ q.2)
      (fun q => ν q.1 * δ q.2))
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) {t : LB.Gen (LB.LinComb M φ δ)} (ht : t.IsGen)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {I I' : (Y ⟶ X) → M.ι} {jM jM' : K → M'.ι}
    (h : r z ∈ wG (pr := pr) (εp := εp) φ' (φ := φ) ρ I jM) (h' : r z ∈ wG (pr := pr) (εp := εp) φ' (φ := φ) ρ I' jM') :
    ratioG w ρ ν t' t r z I jM = ratioG w ρ ν t' t r z I' jM' := by
  have e₁ : ∀ a, bwE w (r ≫ φ' a) z (fun i => I (φ' a ≫ pr i)) (jM a) = _ := fun a =>
    bwE_trans w hw (r ≫ φ' a) z (jN' := fun i => I' (φ' a ≫ pr i)) (k' := jM' a)
      (Set.mem_iInter.1 h.1.1 a) (Set.mem_iInter.1 h'.1.1 a) (Set.mem_iInter.1 h.1.2 a) (Set.mem_iInter.1 h'.1.2 a)
  have e₂ := gen_trans ht' r z h.1.2 h'.1.2
  have e₃ : ∀ p, gm (r ≫ ρ p) z (LB.wchart M φ (fun k => I (ρ p ≫ φ k))) (t.s (fun k => I (ρ p ≫ φ k))) = _ :=
    fun p => gen_trans ht (r ≫ ρ p) z (j' := fun k => I' (ρ p ≫ φ k)) (chart_leG ρ I p h.2) (chart_leG ρ I' p h'.2)
  have e₄ : ∏ a, (∏ i, gm ((r ≫ φ' a) ≫ pr i) z (M.U (I (φ' a ≫ pr i)) ⊓ M.U (I' (φ' a ≫ pr i)))
        (M.g (I (φ' a ≫ pr i)) (I' (φ' a ≫ pr i))) ^ εp i) ^ ε a =
      ∏ p, trF φ δ (r ≫ ρ p) z (fun k => I (ρ p ≫ φ k)) (fun k => I' (ρ p ≫ φ k)) ^ ν p := by
    have := hF.trF (L := M) r z I I'
    unfold trF at this ⊢
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type] at this
    refine Eq.trans ?_ (this.trans ?_)
    · refine Finset.prod_congr rfl fun a _ => ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← zpow_mul, mul_comm, Category.assoc]
    · refine Finset.prod_congr rfl fun p _ => ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_mul]
      dsimp only
      rw [mul_comm (δ k), Category.assoc]
  unfold ratioG
  rw [Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) (e₁ a), e₂,
    Finset.prod_congr rfl fun p _ => congrArg (· ^ ν p) (e₃ p)]
  simp only [mul_zpow, Finset.prod_mul_distrib] at e₄ ⊢
  rw [e₄]
  simp only [inv_zpow, Finset.prod_inv_distrib, trF]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Gen2

section Gen3

variable {X X' Y Y₀ : Scheme.{0}} {M : LB X} {M' : LB X'} {P : Type} [Fintype P] {pr : P → (X' ⟶ X)} {εp : P → ℤ}
  {K : Type} [Fintype K] {Q : Type} [Fintype Q] {P₂ : Type} [Fintype P₂]

theorem box_uniqueG {S₀ : Scheme.{0}} (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr εp))
    (hw : w.IsGen) {φ' : K → (Y ⟶ X')} {ε : K → ℤ} {φ : Q → (Y₀ ⟶ X)} {δ : Q → ℤ} {ρ : P₂ → (Y ⟶ Y₀)} {ν : P₂ → ℤ}
    (hF : FormEq (fun q : K × P => φ' q.1 ≫ pr q.2) (fun q => ε q.1 * εp q.2) (fun q : P₂ × Q => ρ q.1 ≫ φ q.2)
      (fun q => ν q.1 * δ q.2))
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) {t : LB.Gen (LB.LinComb M φ δ)} (ht : t.IsGen)
    (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    (h : ∀ y J J', Good M y J → Good M' y J' →
      (∏ a, bwE w (e ≫ φ' a) y (fun i => J ((e ≫ φ' a) ≫ pr i)) (J' (e ≫ φ' a)) ^ ε a) * val t' e y J' =
        ∏ q, val t (e ≫ ρ q) y J ^ ν q)
    (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J') (hJ : Good M z J) (hJ' : Good M' z J') :
    (∏ a, bwE w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r z J' =
      ∏ q, val t (r ≫ ρ q) z J ^ ν q := by
  choose u hu using fun q : ((Y ⟶ X) → M.ι) × (K → M'.ι) => exists_ratioG (pr := pr) (εp := εp) w ρ ν t' t q.1 q.2
  obtain ⟨s, hs⟩ := glue_unit (⊤ : Y.Opens) (fun q : ((Y ⟶ X) → M.ι) × (K → M'.ι) =>
      wG (pr := pr) (εp := εp) φ' (φ := φ) ρ q.1 q.2) (fun _ => le_top)
    (fun y _ => by
      choose I hI using fun χ : Y ⟶ X => exists_chart hM (χ y)
      choose b hb using fun k => exists_chart hM' (φ' k y)
      exact Opens.mem_iSup.2 ⟨(I, b), ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hI (φ' a ≫ pr i),
        Set.mem_iInter.2 hb⟩, Set.mem_iInter.2 fun q => hI (ρ q.1 ≫ φ q.2)⟩) u
    (fun q q' y hy => (hu q _ (𝟙 Y) y hy.1).trans ((ratioG_trans w hw hF ht' ht (𝟙 Y) y hy.1 hy.2).trans
      (hu q' _ (𝟙 Y) y hy.2).symm))
  obtain ⟨a, ha⟩ := hp s.val
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J'), Good M z J → Good M' z J' →
      ((∏ a, bwE w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r z J' *
        (∏ q, val t (r ≫ ρ q) z J ^ ν q)⁻¹).val = gs (r ≫ p) z ⊤ a := by
    intro Z r z J J' hJ hJ'
    have hm : r z ∈ wG (pr := pr) (εp := εp) φ' (φ := φ) ρ (fun χ => J (r ≫ χ)) (fun a => J' (r ≫ φ' a)) :=
      ⟨⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ (r ≫ φ' a ≫ pr i), hJ'.mem _ r⟩,
        hJ.mem (fun q : P₂ × Q => ρ q.1 ≫ φ q.2) r⟩
    have v : ∏ q, val t (r ≫ ρ q) z J ^ ν q = ∏ q, gm (r ≫ ρ q) z (LB.wchart M φ (fun k => J (r ≫ ρ q ≫ φ k)))
        (t.s (fun k => J (r ≫ ρ q ≫ φ k))) ^ ν q := Finset.prod_congr rfl fun q _ =>
      congrArg (· ^ ν q) (val_of t _ z J _ (fun k => by rw [Category.assoc]))
    have vb : ∏ a, bwE w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a =
        ∏ a, bwE w (r ≫ φ' a) z (fun i => J (r ≫ φ' a ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a := by
      simp only [Category.assoc]
    rw [v, vb]
    have w₁ := (hu ((fun χ => J (r ≫ χ)), (fun a => J' (r ≫ φ' a))) Z r z hm).symm.trans
      ((congrArg (gm r z _) (hs _).symm).trans (gm_res r z le_top hm s))
    exact (congrArg Units.val w₁).trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))
  have a1 : a = 1 := fn_ext fun y _ => by
    choose I hI using fun χ : S₀ ⟶ X => exists_chart hM (χ y)
    choose I' hI' using fun χ : S₀ ⟶ X' => exists_chart hM' (χ y)
    have := key _ e y I I' hI hI'
    rw [h y I I' hI hI', mul_inv_cancel, he] at this
    rw [← this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
  have := key Z r z J J' hJ hJ'
  rw [a1, gs_eq _ z ⊤ trivial, map_one, map_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

end Gen3

section Spec

variable {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {D' : DegPre R} {r : ℕ}

def rhoC (pr : Fin r → (D'.P.A ⟶ Q.B)) : (Fin r × Fin r) × Fin 2 → (D'.P.A.left ⟶ (G3 Q.B).left) := fun q =>
  ![(lift (pr q.1.1) (lift (pr q.1.1)⁻¹ (pr q.1.2))).left, (lift (pr q.1.2) (lift (pr q.1.2)⁻¹ (pr q.1.1)⁻¹)).left] q.2

def nuC (W : Matrix (Fin r) (Fin r) ℤ) : (Fin r × Fin r) × Fin 2 → ℤ := fun q => ![W q.1.1 q.1.2, -W q.1.1 q.1.2] q.2

theorem inv_left (pr : Fin r → (D'.P.A ⟶ Q.B)) (hpr : ∀ i, IsMonHom (pr i)) (i : Fin r) :
    (ι[D'.P.A]).left ≫ (pr i).left = ((pr i)⁻¹).left := by
  have := hpr i
  rw [← Over.comp_left, GrpObj.inv_hom, Hom.inv_def]

theorem inv_left_mul (pr : Fin r → (D'.P.A ⟶ Q.B)) (hpr : ∀ i, IsMonHom (pr i)) (i j : Fin r) :
    (ι[D'.P.A]).left ≫ (pr i * pr j).left = ((pr i)⁻¹ * (pr j)⁻¹).left := by
  have := hpr i
  have := hpr j
  rw [← Over.comp_left, MonObj.comp_mul, GrpObj.inv_hom, GrpObj.inv_hom, Hom.inv_def, Hom.inv_def]

theorem inv_left_one : (ι[D'.P.A]).left ≫ (1 : D'.P.A ⟶ Q.B).left = (1 : D'.P.A ⟶ Q.B).left := by
  rw [← Over.comp_left, MonObj.comp_one]

end Spec

section Spec2

variable {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {D' : DegPre R} {r : ℕ}

theorem cub_pow {T : Over (Sp R)} {U : Type} [CommGroup U] (h : (T.left ⟶ Q.B.left) → U) (g : T.left ⟶ (G3 Q.B).left)
    (n : ℤ) : ∏ I : thK.{0}, h (g ≫ thφ Q.B (x3 Q.B) I) ^ (n * thε I) =
      (∏ I : thK.{0}, h (g ≫ thφ Q.B (x3 Q.B) I) ^ thε I) ^ n := by
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun I _ => ?_
  rw [mul_comm, zpow_mul]

theorem formEq_tens (pr : Fin r → (D'.P.A ⟶ Q.B)) (hpr : ∀ i, IsMonHom (pr i)) (W : Matrix (Fin r) (Fin r) ℤ) :
    FormEq (fun q : Fin 2 × ((Fin r × Fin r) × Fin 4) =>
        (![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] : Fin 2 → (D'.P.A.left ⟶ D'.P.A.left)) q.1 ≫ tensφ pr q.2)
      (fun q => (![1, -1] : Fin 2 → ℤ) q.1 * tensε W q.2)
      (fun q : ((Fin r × Fin r) × Fin 2) × thK.{0} => rhoC pr q.1 ≫ thφ Q.B (x3 Q.B) q.2)
      (fun q => nuC W q.1 * thε q.2) := by
  intro U _ h
  refine (Fintype.prod_prod_type _).trans (Finset.prod_comm.trans ((Fintype.prod_prod_type _).trans ?_))
  refine Eq.trans ?_ ((Fintype.prod_prod_type _).trans (Fintype.prod_prod_type _)).symm
  refine Finset.prod_congr rfl fun ij _ => ?_
  simp only [Fin.prod_univ_two]
  rw [cub_pow, cub_pow]
  simp only [rhoC, nuC, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [prod_cub, prod_cub]
  simp only [Fin.prod_univ_four, tensφ, tensε, lamPts, Oε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Category.id_comp]
  rw [inv_left_mul pr hpr, inv_left pr hpr, inv_left pr hpr, inv_left_one]
  rw [mul_inv_cancel (pr ij.1), mul_inv_cancel (pr ij.2), _root_.one_mul (pr ij.2), _root_.one_mul (pr ij.1)⁻¹,
    mul_comm (pr ij.1)⁻¹ (pr ij.2), mul_comm (pr ij.2)⁻¹ (pr ij.1)⁻¹]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, _root_.one_mul, _root_.mul_one, neg_mul, mul_neg, neg_neg, neg_smul,
    smul_add, smul_sub, smul_neg, one_smul]
  abel

end Spec2

section Spec3

variable {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {D' : DegPre R} {r : ℕ}

theorem eta_one (B : Over (Sp R)) [GrpObj B] : (η[B] : 𝟙_ (Over (Sp R)) ⟶ B) = 1 := by
  rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

theorem eSec_rhoC (pr : Fin r → (D'.P.A ⟶ Q.B)) (hpr : ∀ i, IsMonHom (pr i)) (p : (Fin r × Fin r) × Fin 2) :
    eSec D'.P.A ≫ rhoC pr p = (lift (1 : 𝟙_ (Over (Sp R)) ⟶ Q.B) (lift 1 1)).left := by
  have h1 : ∀ i, η[D'.P.A] ≫ pr i = 1 := fun i => by
    have := hpr i
    rw [IsMonHom.one_hom, eta_one]
  have h2 : ∀ i, η[D'.P.A] ≫ (pr i)⁻¹ = 1 := fun i => by rw [GrpObj.comp_inv, h1, inv_one]
  obtain ⟨⟨i, j⟩, s⟩ := p
  fin_cases s
  · show (η[D'.P.A]).left ≫ (lift (pr i) (lift (pr i)⁻¹ (pr j))).left = _
    rw [← Over.comp_left, comp_lift, comp_lift, h1, h2, h1]
  · show (η[D'.P.A]).left ≫ (lift (pr j) (lift (pr j)⁻¹ (pr i)⁻¹)).left = _
    rw [← Over.comp_left, comp_lift, comp_lift, h1, h2, h2]

theorem sym_tensP (hG : GlobalFnsSt) (pr : Fin r → (D'.P.A ⟶ Q.B)) (hpr : ∀ i, IsMonHom (pr i))
    (W : Matrix (Fin r) (Fin r) ℤ) (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))) (hw : w.IsGen)
    {Z : Scheme.{0}} (q : Z ⟶ D'.P.A.left) (y : Z) {J J'} (hJ : Good Q.M.L y J) (hJ' : Good D'.P.L y J') :
    bwE w (q ≫ (ι[D'.P.A]).left) y (fun k => J ((q ≫ (ι[D'.P.A]).left) ≫ tensφ pr k)) (J' (q ≫ (ι[D'.P.A]).left)) *
      (bwE w q y (fun k => J (q ≫ tensφ pr k)) (J' q))⁻¹ * val D'.sym q y J' =
      ∏ p, val (L := Q.M.L) (φ := thφ Q.B (x3 Q.B)) (ε := thε) Q.cub.t (q ≫ rhoC pr p) y J ^ nuC W p := by
  have pp : ∀ {Z : Scheme.{0}} (r : Z ⟶ D'.P.A.left) {U : Type} [CommGroup U] (f : (Z ⟶ D'.P.A.left) → U),
      ∏ a : Fin 2, f (r ≫ (![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] : Fin 2 → (D'.P.A.left ⟶ D'.P.A.left)) a) ^
        (![1, -1] : Fin 2 → ℤ) a = f (r ≫ (ι[D'.P.A]).left) * (f r)⁻¹ := fun r U _ f => by
    simp [Fin.prod_univ_two]
  have key := box_uniqueG Q.M.isLB D'.P.isLB w hw (formEq_tens pr hpr W) D'.sym_gen Q.cub.isGen D'.P.A.hom
    (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2
    (fun s I I' hI hI' => by
      have q' := pp (Z := Spec (CommRingCat.of R)) (eSec D'.P.A)
        (fun ψ => bwE w ψ s (fun i => I (ψ ≫ tensφ pr i)) (I' ψ))
      have o : eSec D'.P.A ≫ (ι[D'.P.A]).left = eSec D'.P.A :=
        congrArg (fun m => m.left) (GrpObj.one_inv : η[D'.P.A] ≫ ι[D'.P.A] = η[D'.P.A])
      rw [o, mul_inv_cancel] at q'
      have v' := val_corr hI' D'.sym_rig (𝟙 _)
      rw [val_pull hI', Category.id_comp, val_one] at v'
      refine (congrArg₂ (· * ·) q' v').trans (Eq.trans (by simp) (Finset.prod_eq_one fun p _ => ?_).symm)
      rw [eSec_rhoC pr hpr p]
      exact (congrArg (· ^ nuC W p) ((isCub_cubV Q.cub (T := 𝟙_ (Over (Sp R))) hI).face 1 1)).trans (one_zpow _))
    _ q y J J' hJ hJ'
  exact (congrArg₂ (· * ·) (pp q (fun ψ => bwE w ψ y (fun i => J (ψ ≫ tensφ pr i)) (J' ψ))) rfl).symm.trans key

end Spec3

section Main

variable {R : Type} [CommRing R] [IsDomain R]

theorem c_zeroQ (Q : Data R) : Q.c 0 = 1 := mul_eq_left.1 ((Q.c_add 0 0).symm.trans (by rw [add_zero]))

theorem c_negQ (Q : Data R) (a : Q.X) : Q.c (-a) = (Q.c a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← Q.c_add, neg_add_cancel, c_zeroQ]

theorem pt_negQ (Q : Data R) (a : Q.X) : toUnit (TK R) ≫ Q.c (-a) = (toUnit (TK R) ≫ Q.c a)⁻¹ := by
  rw [c_negQ, GrpObj.comp_inv]

theorem tau_negQ (Q : Data R) (a b : Q.X) (y : (TK R).left) (J) (hJ : Good Q.M.L y J) :
    val (Q.tau (-a) (-b)) (𝟙 _) y J *
      (cubV Q.cub y J (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c (-a)) (toUnit (TK R) ≫ Q.c b) *
        (cubV Q.cub y J (toUnit (TK R) ≫ Q.c b) (toUnit (TK R) ≫ Q.c (-b)) (toUnit (TK R) ≫ Q.c (-a)))⁻¹) =
      val (Q.tau a b) (𝟙 _) y J := by
  have t₁ := Q.tau_add a (-a) b y J hJ
  have t₂ := Q.tau_add b (-b) (-a) y J hJ
  rw [add_neg_cancel, Q.val_tau_zero _ y J hJ, _root_.one_mul] at t₁ t₂
  have s₁ := Q.tau_symm (-b) (-a) y J hJ
  have s₂ := Q.tau_symm b (-a) y J hJ
  apply Additive.ofMul.injective
  have E := fun {p q : ((TK R).left.presheaf.stalk y)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E t₁; have a₂ := E t₂; have b₁ := E s₁; have b₂ := E s₂
  simp only [ofMul_mul, ofMul_inv] at a₁ a₂ b₁ b₂ ⊢
  linear_combination (norm := abel) a₁ - a₂ - b₁ - b₂

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ}
    (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) →
    IsLimit (Fan.mk D'.P.A pr) → ∀ (xe : D'.X ≃+ (Fin r → Q.X)), (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) →
    ∀ (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), w.IsGen →
    (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' →
      val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → D'.PsiEven := by
  intro R _ _ _ _ Q D' r W pr hpr _ xe hc w hw hpsi x
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  choose J hJ using fun ψ : (TK R).left ⟶ Q.B.left => exists_chart Q.M.isLB (ψ y)
  have hJ : Good Q.M.L y J := hJ
  rw [val_mul hJ', val_pull hJ', Category.id_comp]
  have key := sym_tensP GlobalTheory.globalFns_holds pr hpr W w hw (D'.xK x) y hJ hJ'
  have b₁ := hpsi x y J J' hJ hJ'
  have b₂ := hpsi (-x) y J J' hJ hJ'
  have n : D'.xK (-x) = D'.xK x ≫ (ι[D'.P.A]).left := by
    show (toUnit (TK R) ≫ D'.c (-x)).left = _
    rw [GlobalTheory.PsiEvenPull.c_neg, ← Category.assoc, Over.comp_left]
  rw [← n] at key
  have hu : ∀ i, (toUnit (TK R) ≫ D'.c x) ≫ pr i = toUnit (TK R) ≫ Q.c (xe x i) := fun i => by
    rw [Category.assoc, hc]
  have hu' : ∀ i, (toUnit (TK R) ≫ D'.c x) ≫ (pr i)⁻¹ = toUnit (TK R) ≫ Q.c (-(xe x i)) := fun i => by
    rw [GrpObj.comp_inv, hu, pt_negQ]
  have vC : ∀ i j, val (L := Q.M.L) (φ := thφ Q.B (x3 Q.B)) (ε := thε) Q.cub.t (D'.xK x ≫ rhoC pr ((i, j), 0)) y J ^
        nuC W ((i, j), 0) * val (L := Q.M.L) (φ := thφ Q.B (x3 Q.B)) (ε := thε) Q.cub.t
          (D'.xK x ≫ rhoC pr ((i, j), 1)) y J ^ nuC W ((i, j), 1) =
      (cubV Q.cub y J (toUnit (TK R) ≫ Q.c (xe x i)) (toUnit (TK R) ≫ Q.c (-(xe x i))) (toUnit (TK R) ≫ Q.c (xe x j)) *
        (cubV Q.cub y J (toUnit (TK R) ≫ Q.c (xe x j)) (toUnit (TK R) ≫ Q.c (-(xe x j)))
          (toUnit (TK R) ≫ Q.c (-(xe x i))))⁻¹) ^ W i j := by
    intro i j
    have e₀ : D'.xK x ≫ rhoC pr ((i, j), 0) = (lift (toUnit (TK R) ≫ Q.c (xe x i))
        (lift (toUnit (TK R) ≫ Q.c (-(xe x i))) (toUnit (TK R) ≫ Q.c (xe x j)))).left := by
      show (toUnit (TK R) ≫ D'.c x).left ≫ (lift (pr i) (lift (pr i)⁻¹ (pr j))).left = _
      rw [← Over.comp_left, comp_lift, comp_lift, hu, hu', hu]
    have e₁ : D'.xK x ≫ rhoC pr ((i, j), 1) = (lift (toUnit (TK R) ≫ Q.c (xe x j))
        (lift (toUnit (TK R) ≫ Q.c (-(xe x j))) (toUnit (TK R) ≫ Q.c (-(xe x i))))).left := by
      show (toUnit (TK R) ≫ D'.c x).left ≫ (lift (pr j) (lift (pr j)⁻¹ (pr i)⁻¹)).left = _
      rw [← Over.comp_left, comp_lift, comp_lift, hu, hu', hu']
    rw [e₀, e₁]
    simp only [nuC, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [mul_zpow, inv_zpow, zpow_neg]
    rfl
  have Qe : ∏ p, val (L := Q.M.L) (φ := thφ Q.B (x3 Q.B)) (ε := thε) Q.cub.t (D'.xK x ≫ rhoC pr p) y J ^ nuC W p =
      ∏ i, ∏ j, (cubV Q.cub y J (toUnit (TK R) ≫ Q.c (xe x i)) (toUnit (TK R) ≫ Q.c (-(xe x i)))
          (toUnit (TK R) ≫ Q.c (xe x j)) *
        (cubV Q.cub y J (toUnit (TK R) ≫ Q.c (xe x j)) (toUnit (TK R) ≫ Q.c (-(xe x j)))
          (toUnit (TK R) ≫ Q.c (-(xe x i))))⁻¹) ^ W i j := by
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => (Fin.prod_univ_two _).trans (vC i j)
  have hn : ∀ i, xe (-x) i = -xe x i := fun i => by rw [map_neg]; rfl
  have E : (∏ i, ∏ j, val (Q.tau (xe (-x) i) (xe (-x) j)) (𝟙 _) y J ^ W i j) *
      ∏ p, val (L := Q.M.L) (φ := thφ Q.B (x3 Q.B)) (ε := thε) Q.cub.t (D'.xK x ≫ rhoC pr p) y J ^ nuC W p =
      ∏ i, ∏ j, val (Q.tau (xe x i) (xe x j)) (𝟙 _) y J ^ W i j := by
    rw [Qe, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← mul_zpow, hn, hn, tau_negQ Q (xe x i) (xe x j) y J hJ]
  rw [b₁, b₂]
  exact alg _ _ _ _ _ _ key E

end Main

end GlobalTheory.PolTensEven
