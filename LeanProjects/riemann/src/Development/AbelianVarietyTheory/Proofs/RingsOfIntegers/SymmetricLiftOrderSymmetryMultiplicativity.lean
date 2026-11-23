import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGrpPullback

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

namespace GlobalTheory.TransUnit.Laws

section Alg
variable {Γ₀ Γ F U I : Type} [CommGroup Γ₀] [CommGroup Γ] [CommGroup F] [CommGroup U]

theorem lineCoeffCubic_mem (M : Subgroup U) {q : Γ → U} (h : ∀ x, q x ∈ M) (x y z : Γ) : c3 q x y z ∈ M :=
  M.div_mem (M.mul_mem (M.mul_mem (M.mul_mem (h _) (h _)) (h _)) (h _)) (M.mul_mem (M.mul_mem (h _) (h _)) (h _))

theorem quadQ_mem (M : Subgroup U) {p : Γ → Γ → Γ → U} (h : ∀ x y z, p x y z ∈ M) (w : Γ → Γ) (x y z : Γ) :
    quadQ p p w x y z ∈ M :=
  have hT : ∀ x y, quadT p p w x y ∈ M := fun _ _ => M.mul_mem (M.mul_mem (h _ _ _) (h _ _ _)) (h _ _ _)
  M.mul_mem (M.mul_mem (M.div_mem (hT _ _) (M.mul_mem (hT _ _) (hT _ _))) (h _ _ _)) (h _ _ _)

theorem quadN_mem (M : Subgroup U) {p : Γ → Γ → Γ → U} (h : ∀ x y z, p x y z ∈ M) (w : Γ → Γ) (x : Γ) :
    quadN p p w x ∈ M := M.div_mem (h _ _ _) (h _ _ _)

def lam (b : Γ → F) (x y : Γ) : F := b (x * y) * (b x)⁻¹ * (b y)⁻¹ * b 1

def cube (b : Γ → F) (x y z : Γ) : F :=
  b (x * y * z) * (b (x * y))⁻¹ * (b (x * z))⁻¹ * (b (y * z))⁻¹ * b x * b y * b z * (b 1)⁻¹

theorem cube_eq₁ (b : Γ → F) (x y z : Γ) : cube b x y z = 1 * (lam b (x * y) z / (lam b x z * lam b y z)) := by
  apply Additive.ofMul.injective
  simp only [cube, lam, ofMul_mul, ofMul_div, ofMul_inv, ofMul_one]
  abel

theorem cube_eq₂ (b : Γ → F) (x y z : Γ) : cube b x y z = 1 * (lam b x (y * z) / (lam b x y * lam b x z)) := by
  apply Additive.ofMul.injective
  simp only [cube, lam, ← _root_.mul_assoc x y z, ofMul_mul, ofMul_div, ofMul_inv, ofMul_one]
  abel

theorem lam_one_left (b : Γ → F) (x : Γ) : lam b 1 x = 1 := by
  apply Additive.ofMul.injective
  simp only [lam, _root_.one_mul, ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem lam_one_right (b : Γ → F) (x : Γ) : lam b x 1 = 1 := by
  apply Additive.ofMul.injective
  simp only [lam, _root_.mul_one, ofMul_mul, ofMul_inv, ofMul_one]
  abel

variable (P : I → (Γ₀ →* Γ)) (b : Γ₀ → F) (w₀ : Γ₀ →* Γ₀) {w : Γ → Γ} (hw : ∀ i x, w (P i x) = P i (w₀ x))
  (M : Subgroup (F × (I → U))) (hM : ∀ q ∈ M, q.1 = 1 → ∀ i j, q.2 i = q.2 j)
  {θ : Γ → Γ → Γ → U} (C : IsCub θ) {ρ : Γ → U}
  (hθ : ∀ x y z, (cube b x y z, fun i => θ (P i x) (P i y) (P i z)) ∈ M)
  (hρ : ∀ x, (b x * (lam b x (w₀ x))⁻¹, fun i => ρ (P i x)) ∈ M)
  {X Y : Γ₀} (hs : ∀ x y, ∃ i, P i X = x ∧ P i Y = y) (k : ℕ)
include hw hM C hθ hρ hs

theorem sym_law {ν : Γ → U} (hν : ∀ x, (b x ^ k * (b x⁻¹ ^ k)⁻¹, fun i => ν (P i x)) ∈ M) (x : Γ) :
    ν x⁻¹ * (ρ x / ρ x⁻¹ * quadN θ θ w x) ^ k = ν 1 := by
  let θ' := fun x y z => ((cube b x y z, fun i => θ (P i x) (P i y) (P i z)) : F × (I → U))
  have hq := M.mul_mem (hν X⁻¹) (M.pow_mem (M.mul_mem (M.div_mem (hρ X) (hρ X⁻¹)) (quadN_mem M hθ w₀ X)) k)
  have e₁ : (quadN θ' θ' w₀ X).1 = lam b X (w₀ X) / lam b X⁻¹ (w₀ X⁻¹) :=
    (quadN_of_diff w₀ (cube_eq₁ b) (cube_eq₂ b) (lam_one_left b) (lam_one_right b) X).trans
      (by rw [quadN_one, _root_.one_mul])
  have e₂ : ∀ i, (quadN θ' θ' w₀ X).2 i = quadN θ θ w (P i X) := fun i =>
    (quadN_map (P i) ((Pi.evalMonoidHom (fun _ => U) i).comp (MonoidHom.snd F _)) (p₁ := θ') (p₂ := θ') (hw i)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) X).symm
  obtain ⟨i, hi, -⟩ := hs x 1
  obtain ⟨j, hj, -⟩ := hs 1 1
  have h := hM _ hq (by
    simp only [Prod.fst_mul, Prod.pow_fst, Prod.fst_div]
    rw [e₁, inv_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_one, ofMul_pow]
    module) i j
  simp only [Prod.snd_mul, Prod.pow_snd, Prod.snd_div, Pi.mul_apply, Pi.pow_apply, Pi.div_apply] at h
  rw [e₂, e₂, map_inv, map_inv, hi, hj] at h
  rw [h, quadN, inv_one, C.face, C.face, div_self', div_self', _root_.mul_one, one_pow, _root_.mul_one]

theorem mul_law {φ : Γ → U} {a₀ : Γ₀} {a : Γ} (ha : ∀ i, P i a₀ = a)
    (hφ : ∀ x, (b x ^ k * (b (a₀ * x) ^ k)⁻¹, fun i => φ (P i x)) ∈ M) (x y : Γ) :
    φ (x * y) * φ 1 * (c3 ρ x y a / ρ 1 * quadQ θ θ w x y a) ^ k = φ x * φ y := by
  let θ' := fun x y z => ((cube b x y z, fun i => θ (P i x) (P i y) (P i z)) : F × (I → U))
  let ρ' := fun x => ((b x * (lam b x (w₀ x))⁻¹, fun i => ρ (P i x)) : F × (I → U))
  have hq := M.div_mem (M.mul_mem (M.mul_mem (hφ (X * Y)) (hφ 1)) (M.pow_mem (M.mul_mem
    (M.div_mem (lineCoeffCubic_mem M hρ X Y a₀) (hρ 1)) (quadQ_mem M hθ w₀ X Y a₀)) k)) (M.mul_mem (hφ X) (hφ Y))
  have e₁ : (quadQ θ' θ' w₀ X Y a₀).1 = c3 (fun x => lam b x (w₀ x)) X Y a₀ :=
    (quadQ_of_diff w₀ (cube_eq₁ b) (cube_eq₂ b) X Y a₀).trans (by rw [quadQ_one, _root_.one_mul])
  have e₂ : ∀ i, (quadQ θ' θ' w₀ X Y a₀).2 i = quadQ θ θ w (P i X) (P i Y) (P i a₀) := fun i =>
    (quadQ_map (P i) ((Pi.evalMonoidHom (fun _ => U) i).comp (MonoidHom.snd F _)) (p₁ := θ') (p₂ := θ') (hw i)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) X Y a₀).symm
  have e₃ : (c3 ρ' X Y a₀).1 = c3 (fun x => b x * (lam b x (w₀ x))⁻¹) X Y a₀ := rfl
  have e₄ : ∀ i, (c3 ρ' X Y a₀).2 i = c3 ρ (P i X) (P i Y) (P i a₀) := fun i =>
    (map_lineCoeffCubic (P i) ((Pi.evalMonoidHom (fun _ => U) i).comp (MonoidHom.snd F _)) (q := ρ') (fun _ => rfl) X Y a₀).symm
  obtain ⟨i, hi, hi'⟩ := hs x y
  obtain ⟨j, hj, hj'⟩ := hs 1 1
  have w₁ : w 1 = 1 := by simpa only [map_one] using hw i 1
  have h := hM _ hq (by
    simp only [Prod.fst_mul, Prod.pow_fst, Prod.fst_div]
    rw [e₁, e₃, lam_one_left, _root_.mul_one a₀, mul_comm a₀, mul_comm a₀, mul_comm a₀]
    apply Additive.ofMul.injective
    simp only [c3, ofMul_mul, ofMul_div, ofMul_inv, ofMul_one, ofMul_pow]
    module) i j
  simp only [Prod.snd_mul, Prod.pow_snd, Prod.snd_div, Pi.mul_apply, Pi.pow_apply, Pi.div_apply] at h
  rw [e₂, e₂, e₄, e₄] at h
  simp only [map_mul, map_one, hi, hi', hj, hj', ha] at h
  refine div_eq_one.1 (h.trans ?_)
  simp only [quadQ, quadT, c3, w₁, C.face, C.face₂, _root_.mul_one, _root_.one_mul, div_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_one, ofMul_pow]
  module

end Alg

section Pairs
variable {X Y Z : Scheme.{0}} {L : LB X} {z : Z} {J : (Z ⟶ X) → L.ι} {I : Type}

def fs (ψ : Y ⟶ X) : Multiplicative (FreeAbelianGroup (Y ⟶ X)) := Multiplicative.ofAdd (FreeAbelianGroup.of ψ)

theorem oneGen_isGen : (LB.oneGen L (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

def pairs (hJ : Good L z J) (r : I → (Z ⟶ Y)) :
    Subgroup (Multiplicative (FreeAbelianGroup (Y ⟶ X)) × (I → (Z.presheaf.stalk z)ˣ)) where
  carrier := {q | ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (u : LB.Gen (LB.LinComb L φ ε)),
    u.IsGen ∧ ∏ k, fs (φ k) ^ ε k = q.1 ∧ ∀ i, val u (r i) z J = q.2 i}
  one_mem' := ⟨_, _, _, _, LB.oneGen L, oneGen_isGen, Fintype.prod_empty _, fun _ => val_one _⟩
  mul_mem' := by
    rintro p q ⟨K, _, φ, ε, u, hu, f, v⟩ ⟨K', _, φ', ε', u', hu', f', v'⟩
    exact ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ u u', DVR.mulGen_isGen _ _ _ _ _ _ _ hu hu',
      (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) f f'),
      fun i => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v i) (v' i))⟩
  inv_mem' := by
    rintro p ⟨K, _, φ, ε, u, hu, f, v⟩
    refine ⟨K, inferInstance, _, _, LB.invGen L _ _ u, DVR.invGen_isGen _ _ _ _ hu, ?_,
      fun i => (val_inv _ _).trans (congrArg (·⁻¹) (v i))⟩
    simp only [zpow_neg, Finset.prod_inv_distrib, f, Prod.fst_inv]

theorem pairs_const (hL : L.IsLB) (hJ : Good L z J) (r : I → (Z ⟶ Y)) {S₀ : Scheme.{0}} (p : Y ⟶ S₀)
    (hp : Function.Surjective p.appTop.hom) (hr : ∀ i j, r i ≫ p = r j ≫ p) :
    ∀ q ∈ pairs hJ r, q.1 = 1 → ∀ i j, q.2 i = q.2 j := by
  rintro q ⟨K, _, φ, ε, u, hu, f, v⟩ h1 i j
  obtain ⟨t, ht, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
    let g : Multiplicative (FreeAbelianGroup (Y ⟶ X)) →* U :=
      (FreeAbelianGroup.lift fun ψ => Additive.ofMul (h ψ)).toMultiplicativeLeft
    have hg : ∀ ψ, g (fs ψ) = h ψ := fun ψ => by simp [g, fs]
    have e := congrArg g (f.trans h1)
    simp only [map_prod, map_zpow, map_one, hg] at e
    exact e.trans (Fintype.prod_empty _).symm) u hu
  have e := CommPairing.val_div_eq hL p hp ht oneGen_isGen (r i) (r j) (hr i j) z J hJ
  rwa [val_one, val_one, mul_left_inj, hv _ _ z J hJ, hv _ _ z J hJ, v, v] at e

theorem pull_mem (hJ : Good L z J) (r : I → (Z ⟶ Y)) {Y₀ : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y₀ ⟶ X)}
    {ε : K → ℤ} {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (h : Y ⟶ Y₀) {f} {v : I → (Z.presheaf.stalk z)ˣ}
    (hf : ∏ k, fs (h ≫ φ k) ^ ε k = f) (hv : ∀ i, val u (r i ≫ h) z J = v i) : (f, v) ∈ pairs hJ r :=
  ⟨K, inferInstance, _, _, LB.pullGen L _ _ u h, DVR.pullGen_isGen _ _ _ _ hu _, hf,
    fun i => (val_pull hJ _ _ _).trans (hv i)⟩

end Pairs

end GlobalTheory.TransUnit.Laws

namespace GlobalTheory.TransUnit
open Laws

theorem liftLaws_of_symLift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S), Function.Surjective (t.G ⊗ t.G).hom.appTop.hom → ∀ (wP : PrimTyG t), wP.IsGen → ∀ (k : ℕ) (a : baseOver S ⟶ t.G) (U : ThetaGrp t.G t.PP.L (k : ℤ) (baseOver S)), SymLift t.G t.PP.L (k : ℤ) k a U → ∀ (T : Over S) (σ : T ⟶ baseOver S) (z : T.left) (J : (T.left ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → LiftLaws (cubV t.cub z J) (fun p : T ⟶ t.G => val wP p.left z J) (fun p : T ⟶ t.G => GlobalTheory.CommPairing.tval U (lift σ p).left z J) (fun p : T ⟶ t.G => p ≫ t.act.act H.w0) (σ ≫ a) k := by
  intro E _ _ _ H S t hp wP hw k a U hU T σ z J hJ
  have := t.act.hom H.w0
  have hL := t.PP.isLB
  obtain ⟨ν, hν, hsym⟩ := sym_val hU
  obtain rfl := hU.pt_eq
  let T₀ := t.G ⊗ t.G
  let σ₀ : T₀ ⟶ baseOver S := Over.homMk T₀.hom (Category.comp_id _)
  have hσ : ∀ i : T ⟶ T₀, i ≫ σ₀ = σ := fun i => Over.OverMorphism.ext
    ((Over.w i).trans ((Over.w σ).symm.trans (Category.comp_id _)))
  let r : (T ⟶ T₀) → (T.left ⟶ T₀.left) := fun i => i.left
  let P : (T ⟶ T₀) → ((T₀ ⟶ t.G) →* (T ⟶ t.G)) := fun i => preHom i
  let b := fun x : T₀ ⟶ t.G => fs x.left
  let w₀ : (T₀ ⟶ t.G) →* (T₀ ⟶ t.G) := MonoidHom.mk' (· ≫ t.act.act H.w0) fun x y => MonObj.mul_comp x y _
  have hw₀ : ∀ i x, P i x ≫ t.act.act H.w0 = P i (w₀ x) := fun i x => Category.assoc _ _ _
  have hM := pairs_const hL hJ r T₀.hom hp fun i j => (Over.w i).trans (Over.w j).symm
  have C := isCub_cubV t.cub hJ
  have hl : ∀ (i : T ⟶ T₀) (x : T₀ ⟶ t.G), r i ≫ (lift σ₀ x).left = (lift σ (P i x)).left := fun i x => by
    rw [← hσ i]; exact congrArg (fun q => q.left) (comp_lift i σ₀ x)
  have hθ : ∀ x y z', (cube b x y z', fun i => cubV t.cub z J (P i x) (P i y) (P i z')) ∈ pairs hJ r := fun x y z' =>
    ⟨_, inferInstance, _, _, _, DVR.pullGen_isGen _ _ _ _ t.cub.isGen (lift x (lift y z')).left, prod_cub x y z' fs,
      fun i => val_cub t.cub i hJ x y z'⟩
  have hρ : ∀ x, (b x * (lam b x (w₀ x))⁻¹, fun i => val wP (P i x).left z J) ∈ pairs hJ r := fun x => by
    refine pull_mem hJ r hw x.left ?_ fun i => rfl
    refine (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) ?_ ?_)
    · simp only [Sum.elim_inl, Category.comp_id, zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        pow_one, b]
    · have e := prod_cube₂ (𝟙 t.G) (t.act.act H.w0) fun q => fs (x.left ≫ q)
      simp only [← Over.comp_left, MonObj.comp_mul, MonObj.comp_one, Category.comp_id] at e
      simp only [Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      exact congrArg (·⁻¹) e
  have hs : ∀ x y : T ⟶ t.G, ∃ i, P i (fst t.G t.G) = x ∧ P i (snd t.G t.G) = y := fun x y =>
    ⟨lift x y, lift_fst x y, lift_snd x y⟩
  refine ⟨fun x => ?_, ?_, ?_⟩
  · have e := (ThetaPullback.val_powGen U k (lift σ x).left hJ).symm.trans ((val_corr hJ hU.pow_eq _).trans (val_one _))
    rw [Finset.prod_range]
    refine Eq.trans (Finset.prod_congr rfl fun j _ => ?_) e
    rw [← Over.comp_left, lift_transl, MonObj.comp_pow]; rfl
  · have e := sym_law P b w₀ (w := fun p => p ≫ t.act.act H.w0) hw₀ _ hM C (ρ := fun p => val wP p.left z J) hθ hρ hs k
      (ν := fun p => val (L := t.PP.L)
      (φ := ![(snd (baseOver S) t.G).left, (snd (baseOver S) t.G ≫ (GrpObj.inv : t.G ⟶ t.G)).left])
      (ε := ![(k : ℤ), -k]) ν (lift σ p).left z J)
      (fun x => by
        refine pull_mem hJ r hν (lift σ₀ x).left ((prod_two _ _ _ _ _ fs).trans ?_) fun i => by rw [hl]
        rw [lift_snd, lift_snd_assoc, zpow_neg, zpow_natCast, zpow_natCast]; rfl) (σ ≫ U.pt)
    have e' := (hsym σ hJ).2
    apply Additive.ofMul.injective
    replace e := congrArg Additive.ofMul e
    replace e' := congrArg Additive.ofMul e'
    simp only [CommPairing.tval, ofMul_mul, ofMul_inv, ofMul_one] at e e' ⊢
    linear_combination (norm := abel) e + e'
  · refine mul_law P b w₀ (w := fun p => p ≫ t.act.act H.w0) hw₀ _ hM C (ρ := fun p => val wP p.left z J) hθ hρ hs k
      (φ := fun p => CommPairing.tval U (lift σ p).left z J) (a₀ := σ₀ ≫ U.pt)
      (fun i => (Category.assoc i σ₀ U.pt).symm.trans (congrArg (· ≫ U.pt) (hσ i))) fun x => ?_
    refine pull_mem hJ r (φ := ![(snd (baseOver S) t.G).left, (translPt t.G U.pt).left]) (ε := ![(k : ℤ), -k])
      (u := U.φ) U.isGen (lift σ₀ x).left ((prod_two _ _ _ _ _ fs).trans ?_)
      fun i => congrArg (fun q => CommPairing.tval U q z J) (hl i x)
    rw [lift_snd, translPt_eq, MonObj.comp_mul, lift_fst_assoc, lift_snd, zpow_neg, zpow_natCast, zpow_natCast]

end GlobalTheory.TransUnit
