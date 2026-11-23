import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIntegral

section Gens

variable {S : Scheme.{0}} {X : Scheme.{0}} (M : LB X) (T : Over S)

def HasGen (F : ∀ (U : Type) [CommGroup U], ((T.left ⟶ X) → U) → U)
    (f : ∀ (T' : Over S) (_ : T' ⟶ T) (p : T'.left) (_ : (T'.left ⟶ X) → M.ι), (T'.left.presheaf.stalk p)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (T.left ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb M φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (T.left ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h) ∧
    ∀ (T' : Over S) (σ : T' ⟶ T) (p : T'.left) (J : (T'.left ⟶ X) → M.ι), Good M p J → val t σ.left p J = f T' σ p J

variable {M T}

theorem HasGen.mul {F F' : ∀ (U : Type) [CommGroup U], ((T.left ⟶ X) → U) → U}
    {f f' : ∀ (T' : Over S) (_ : T' ⟶ T) (p : T'.left) (_ : (T'.left ⟶ X) → M.ι), (T'.left.presheaf.stalk p)ˣ}
    (h : HasGen M T F f) (h' : HasGen M T F' f') :
    HasGen M T (fun U _ h => F U h * F' U h) (fun T' σ p J => f T' σ p J * f' T' σ p J) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', hF', hv'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen M _ _ _ _ t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ h => ?_, fun T' σ p J hJ => ?_⟩
  · exact (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (hF U h) (hF' U h))
  · rw [val_mul hJ, hv _ _ _ _ hJ, hv' _ _ _ _ hJ]

theorem HasGen.inv {F : ∀ (U : Type) [CommGroup U], ((T.left ⟶ X) → U) → U}
    {f : ∀ (T' : Over S) (_ : T' ⟶ T) (p : T'.left) (_ : (T'.left ⟶ X) → M.ι), (T'.left.presheaf.stalk p)ˣ}
    (h : HasGen M T F f) :
    HasGen M T (fun U _ h => (F U h)⁻¹) (fun T' σ p J => (f T' σ p J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen M _ _ t, DVR.invGen_isGen _ _ _ _ ht,
    fun U _ h => ?_, fun T' σ p J hJ => ?_⟩
  · simp only [zpow_neg, Finset.prod_inv_distrib, hF]
  · rw [val_inv, hv _ _ _ _ hJ]

theorem HasGen.exists_unit (hM : M.IsLB) {F : ∀ (U : Type) [CommGroup U], ((T.left ⟶ X) → U) → U}
    {f : ∀ (T' : Over S) (_ : T' ⟶ T) (p : T'.left) (_ : (T'.left ⟶ X) → M.ι), (T'.left.presheaf.stalk p)ˣ}
    (h : HasGen M T F f) (hF1 : ∀ (U : Type) [CommGroup U] (h : (T.left ⟶ X) → U), F U h = 1) :
    ∃ w : Γ(T.left, ⊤)ˣ, ∀ (T' : Over S) (σ : T' ⟶ T) (p : T'.left) (J : (T'.left ⟶ X) → M.ι), Good M p J →
      gm σ.left p ⊤ w = f T' σ p J := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := h
  obtain ⟨u, -, vu⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => ((hF U h).trans (hF1 U h)).trans (Fintype.prod_empty _).symm) t ht
  have le : (⊤ : T.left.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (T.left ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (u.s PEmpty.elim), fun T' σ z J hJ => (gm_res σ.left z le trivial _).trans
    ((val_of u σ.left z J PEmpty.elim fun k => k.elim).symm.trans ?_)⟩
  rw [vu _ _ z J hJ, hv _ _ _ _ hJ]

theorem range_subset_of_preimage {Z : Scheme.{0}} {V : X.Opens} {ψ : Z ⟶ X} (h : ψ ⁻¹ᵁ V = ⊤) :
    Set.range ψ ⊆ Set.range V.ι := by
  rintro _ ⟨z, rfl⟩
  have : z ∈ ψ ⁻¹ᵁ V := h ▸ trivial
  exact ⟨⟨ψ z, this⟩, rfl⟩

open Classical in

def genVal {V : X.Opens} (g : LB.Gen (M.pull V.ι)) {Z : Scheme.{0}} (p : Z) (J : (Z ⟶ X) → M.ι) (ψ : Z ⟶ X) :
    (Z.presheaf.stalk p)ˣ :=
  if h : ψ ⁻¹ᵁ V = ⊤ then val g (IsOpenImmersion.lift V.ι ψ (range_subset_of_preimage h)) p J else 1

theorem genVal_comp {V : X.Opens} (g : LB.Gen (M.pull V.ι)) {Z : Scheme.{0}} (p : Z) (J : (Z ⟶ X) → M.ι)
    (r : Z ⟶ V.toScheme) : genVal g p J (r ≫ V.ι) = val g r p J := by
  have h : (r ≫ V.ι) ⁻¹ᵁ V = ⊤ := by
    rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]; rfl
  rw [genVal, dif_pos h]
  congr 1
  rw [← cancel_mono V.ι, IsOpenImmersion.lift_fac]

theorem hasGen_genVal {V : X.Opens} (g : LB.Gen (M.pull V.ι)) (hg : g.IsGen) (ψ : T.left ⟶ X) (hψ : ψ ⁻¹ᵁ V = ⊤) :
    HasGen M T (fun _ _ h => h ψ) (fun _ σ p J => genVal g p J (σ.left ≫ ψ)) := by
  obtain ⟨r, rfl⟩ : ∃ r : T.left ⟶ V.toScheme, r ≫ V.ι = ψ :=
    ⟨_, IsOpenImmersion.lift_fac V.ι ψ (range_subset_of_preimage hψ)⟩
  refine ⟨PUnit, inferInstance, _, _, LB.pullGen M _ _ g r, DVR.pullGen_isGen _ _ _ _ hg _,
    fun U _ h => by simp, fun T' σ p J hJ => ?_⟩
  exact (val_pull hJ _ _ _).trans ((genVal_comp g p J _).symm.trans (congrArg (genVal g p J) (Category.assoc _ _ _)))

end Gens

section Cube

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)

theorem hasGen_cub {T : Over S} (x x' y : T ⟶ A) :
    HasGen L.L T (fun _ _ h => h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ *
        h x.left * h x'.left * h y.left * (h (1 : T ⟶ A).left)⁻¹)
      (fun _ σ p J => cubV c p J (σ ≫ x) (σ ≫ x') (σ ≫ y)) :=
  ⟨thK, inferInstance, _, _, LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift x (lift x' y)).left,
    DVR.pullGen_isGen _ _ _ _ c.isGen _, fun _ _ h => prod_cub x x' y h, fun _ σ _ _ hJ => val_cub c σ hJ x x' y⟩

def diff₂ {G U : Type} [Mul G] [CommGroup U] (h : G → U) (z b d : G) : U :=
  h (z * b * d) * (h (z * b))⁻¹ * (h (z * d))⁻¹ * h z

def cubeVal {G U : Type} [Mul G] [CommGroup U] (θ : G → G → G → U) (h : G → U) (z a b d : G) : U :=
  θ (z * a) b d * (θ z b d)⁻¹ * (diff₂ h (z * a) b d)⁻¹ * diff₂ h z b d

theorem prod_diff₂ {G U : Type} [CommGroup G] [CommGroup U] (h : G → U) (z b d : G) (k : ℕ) :
    ∏ i ∈ Finset.range k, diff₂ h (z * b ^ i) b d =
      h (z * b ^ k * d) * (h (z * b ^ k))⁻¹ * (h (z * d))⁻¹ * h z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, diff₂, pow_succ b, ← _root_.mul_assoc z]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem prod_cubeVal {G U : Type} [CommGroup G] [CommGroup U] {θ : G → G → G → U} (hθ : IsCub θ) (h : G → U)
    (z b d : G) (k : ℕ) (hb : b ^ k = 1) :
    ∏ i ∈ Finset.range k, cubeVal θ h z (b ^ i) b d = cubN θ k 1 b d * ((θ z b d)⁻¹ * diff₂ h z b d) ^ k := by
  have e := hθ.N_split k z b d
  rw [hb, hθ.face₂, _root_.one_mul] at e
  have e' := prod_diff₂ h z b d k
  rw [hb, _root_.mul_one] at e'
  simp only [cubeVal, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_const, Finset.card_range]
  rw [e', ← e, cubN]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, mul_pow]
  module

theorem cubeVal_quot {G U : Type} [CommGroup G] [CommGroup U] {θ : G → G → G → U} (hθ : IsCub θ) (h : G → U)
    (z x y : G) (k : ℕ) (hx : x ^ k = 1) (hy : y ^ k = 1) :
    (∏ i ∈ Finset.range k, cubeVal θ h z (y ^ i) y x) / ∏ i ∈ Finset.range k, cubeVal θ h z (x ^ i) x y =
      cubN θ k 1 y x * (cubN θ k 1 x y)⁻¹ := by
  have d : diff₂ h z y x = diff₂ h z x y := by
    rw [diff₂, diff₂, mul_right_comm z y x, mul_right_comm (h _)]
  rw [prod_cubeVal hθ h z y x k hy, prod_cubeVal hθ h z x y k hx, hθ.s12 z y x, d, mul_div_mul_right_eq_div,
    div_eq_mul_inv]

variable {V : A.left.Opens} (g : LB.Gen (L.L.pull V.ι)) (hg : g.IsGen)

omit [IsCommMonObj A] in
include hg in
theorem hasGen_diff₂ {T : Over S} (z b d : T ⟶ A) (h₀ : InOpen V z) (h₁ : InOpen V (z * b)) (h₂ : InOpen V (z * d))
    (h₃ : InOpen V (z * b * d)) :
    HasGen L.L T (fun _ _ h => diff₂ (fun q : T ⟶ A => h q.left) z b d)
      (fun T' σ p J => diff₂ (fun q : T' ⟶ A => genVal g p J q.left) (σ ≫ z) (σ ≫ b) (σ ≫ d)) := by
  have := (((hasGen_genVal g hg _ h₃).mul (hasGen_genVal g hg _ h₁).inv).mul (hasGen_genVal g hg _ h₂).inv).mul
    (hasGen_genVal g hg _ h₀)
  simpa only [diff₂, ← Over.comp_left, MonObj.comp_mul] using this

include hg in
theorem exists_cube_unit {T : Over S} (z a b d : T ⟶ A) (h : CubeIn V z a b d) :
    ∃ w : Γ(T.left, ⊤)ˣ, ∀ (T' : Over S) (σ : T' ⟶ T) (p : T'.left) (J : (T'.left ⟶ A.left) → L.L.ι), Good L.L p J →
      gm σ.left p ⊤ w = cubeVal (cubV c p J) (fun q : T' ⟶ A => genVal g p J q.left)
        (σ ≫ z) (σ ≫ a) (σ ≫ b) (σ ≫ d) := by
  have D₁ := hasGen_diff₂ g hg (z * a) b d (by simpa using h 1 0 0) (by simpa using h 1 1 0)
    (by simpa using h 1 0 1) (by simpa using h 1 1 1)
  have D₀ := hasGen_diff₂ g hg z b d (by simpa using h 0 0 0) (by simpa using h 0 1 0)
    (by simpa using h 0 0 1) (by simpa using h 0 1 1)
  obtain ⟨w, hw⟩ := ((((hasGen_cub c (z * a) b d).mul (hasGen_cub c z b d).inv).mul D₁.inv).mul D₀).exists_unit
    L.isLB (fun U _ h => by
      apply Additive.ofMul.injective
      simp only [diff₂, ofMul_mul, ofMul_inv, ofMul_one]
      abel)
  refine ⟨w, fun T' σ p J hJ => ?_⟩
  rw [hw T' σ p J hJ, cubeVal, MonObj.comp_mul]

end Cube

section Main

def unitOf {R : Type} [CommRing R] : Γ(Sp R, ⊤)ˣ →* Rˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom

theorem unitOn_unitOf {R : Type} [CommRing R] (w : Γ(Sp R, ⊤)ˣ) : unitOn (unitOf w) = w :=
  Units.ext ((Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply w.val)

theorem unitOf_pull {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (w : Γ(Sp R, ⊤)ˣ) :
    (unitOf (pullU (spMap φ) ⊤ w) : R') = φ (unitOf w : R) := by
  have e := congrArg (fun q => q.hom w.val) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  exact e

theorem hasCubeFn (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (A : Out.PolAV (Sp C)) : HasCubeFn A := by
  classical
  rintro V ⟨g, hg⟩
  have := A.isAb.comm
  have hC : Out.CubeSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.1
  have hG : Out.GlobalFnsSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨r, hr⟩ := A.rigid
  obtain ⟨⟨c⟩, -⟩ := hC _ A ⟨A.L, r, A.isLB, hr⟩ rfl
  choose w hw using fun (T : Over (Sp C)) (z a b d : T ⟶ A.A) (h : CubeIn V z a b d) =>
    exists_cube_unit c g hg z a b d h
  refine ⟨fun S _ t z a b d => if h : CubeIn V z a b d then unitOf (w _ z a b d h) else 1, ?_, ?_⟩
  · intro S S' _ _ φ t t' z a b d z' a' b' d' hz ha hb hd h
    have ht : spMap φ ≫ t = t' := by
      have e₁ : z.left ≫ A.A.hom = t := Over.w z
      have e₂ : z'.left ≫ A.A.hom = t' := Over.w z'
      rw [← e₁, ← e₂, hz]; rfl
    let σ : (Over.mk t' : Over (Sp C)) ⟶ Over.mk t := Over.homMk (spMap φ) ht
    obtain rfl : z' = σ ≫ z := Over.OverMorphism.ext hz
    obtain rfl : a' = σ ≫ a := Over.OverMorphism.ext ha
    obtain rfl : b' = σ ≫ b := Over.OverMorphism.ext hb
    obtain rfl : d' = σ ≫ d := Over.OverMorphism.ext hd
    have h' : CubeIn V (σ ≫ z) (σ ≫ a) (σ ≫ b) (σ ≫ d) := fun i j k hi hj hk => by
      simpa only [MonObj.comp_mul, MonObj.comp_pow] using (h i j k hi hj hk).comp σ
    have e : w _ _ _ _ _ h' = pullU (spMap φ) ⊤ (w _ z a b d h) := Geo.Tor.unit_ext fun p _ => by
      choose J hJ using fun ψ : Sp S' ⟶ A.A.left => exists_chart A.isLB (ψ p)
      have e₁ := hw _ _ _ _ _ h' _ (𝟙 _) p J hJ
      have e₂ := hw _ _ _ _ _ h _ σ p J hJ
      simp only [Category.id_comp] at e₁
      refine e₁.trans (e₂.symm.trans ?_)
      exact ((gm_pull (𝟙 _) (spMap φ) p ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)).symm
    simp only [dif_pos h, dif_pos h']
    rw [e]
    exact unitOf_pull φ _
  · intro N hN x y z hx hy hV
    have h₁ : ∀ i : ℕ, CubeIn V z (y ^ i) y x := fun i j k l _ _ _ => by
      have := hV l (i * j + k)
      rwa [pow_add, pow_mul, mul_right_comm z, ← _root_.mul_assoc] at this
    have h₂ : ∀ i : ℕ, CubeIn V z (x ^ i) x y := fun i j k l _ _ _ => by
      have := hV (i * j + k) l
      rwa [pow_add, pow_mul, ← _root_.mul_assoc] at this
    simp only [dif_pos (h₁ _), dif_pos (h₂ _)]
    obtain ⟨u, hu⟩ := exists_weil c hx hy
    rw [← map_prod, ← map_prod, ← map_div]
    refine ((HTLat.weilIs_iff hN hx hy _).1 ?_).symm
    rw [unitOn_unitOf]
    refine (Geo.Tor.weilIs_iff c hG A.isAb hx hy hu _).2 (Geo.Tor.unit_ext fun p _ => ?_)
    choose J hJ using fun ψ : Sp C ⟶ A.A.left => exists_chart A.isLB (ψ p)
    have e₁ := hu _ (𝟙 _) p J hJ
    have e₂ := fun a b d h => hw _ z a b d h _ (𝟙 _) p J hJ
    simp only [Category.id_comp] at e₁ e₂
    refine Eq.trans ?_ ((cubeVal_quot (isCub_cubV c (T := Over.mk (𝟙 (Sp C))) (z := p) (J := J) hJ)
      (fun q => genVal g p J q.left) z x y N hx hy).trans e₁.symm)
    rw [map_div, map_prod, map_prod]
    exact congrArg₂ (· / ·) (Finset.prod_congr rfl fun i _ => e₂ _ _ _ _) (Finset.prod_congr rfl fun i _ => e₂ _ _ _ _)

end Main

end GlobalTheory.WeilIntegral
