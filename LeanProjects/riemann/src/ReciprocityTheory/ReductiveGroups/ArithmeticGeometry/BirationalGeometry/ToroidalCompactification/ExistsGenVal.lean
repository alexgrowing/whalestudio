import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.MoveQkCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

section Ext

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

@[ext] structure Ex (h : IsCub θ) (c : A) where

  b : A

  u : U

instance (h : IsCub θ) (c : A) : CommGroup (Ex h c) where
  mul p q := ⟨p.b * q.b, p.u * q.u * (θ c p.b q.b)⁻¹⟩
  one := ⟨1, 1⟩
  inv p := ⟨p.b⁻¹, p.u⁻¹ * θ c p.b p.b⁻¹⟩
  mul_assoc p q r := Ex.ext (_root_.mul_assoc _ _ _) (by
    show p.u * q.u * (θ c p.b q.b)⁻¹ * r.u * (θ c (p.b * q.b) r.b)⁻¹ = p.u * (q.u * r.u * (θ c q.b r.b)⁻¹) * (θ c p.b (q.b * r.b))⁻¹
    have e : ∀ x y, θ c x y = θ x y c := fun x y => by rw [h.s01, h.s12]
    have := congrArg Additive.ofMul (h.coc p.b q.b r.b c)
    apply Additive.ofMul.injective
    simp only [e, ofMul_mul, ofMul_inv] at this ⊢
    linear_combination (norm := abel) -this)
  one_mul p := Ex.ext (_root_.one_mul _) (by show 1 * p.u * (θ c 1 p.b)⁻¹ = p.u; rw [h.face₂]; simp)
  mul_one p := Ex.ext (_root_.mul_one _) (by show p.u * 1 * (θ c p.b 1)⁻¹ = p.u; rw [h.face₃]; simp)
  mul_comm p q := Ex.ext (mul_comm _ _) (by
    show p.u * q.u * (θ c p.b q.b)⁻¹ = q.u * p.u * (θ c q.b p.b)⁻¹
    rw [h.s12, mul_comm p.u])
  inv_mul_cancel p := Ex.ext (inv_mul_cancel _) (by
    show p.u⁻¹ * θ c p.b p.b⁻¹ * p.u * (θ c p.b⁻¹ p.b)⁻¹ = 1
    rw [h.s12 c p.b⁻¹, mul_right_comm p.u⁻¹]; simp)

variable {h : IsCub θ} {c : A}

theorem Ex.mul_b (p q : Ex h c) : (p * q).b = p.b * q.b := rfl
theorem Ex.mul_u (p q : Ex h c) : (p * q).u = p.u * q.u * (θ c p.b q.b)⁻¹ := rfl

theorem Ex.pow_b (p : Ex h c) (n : ℕ) : (p ^ n).b = p.b ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ n ih => rw [pow_succ, pow_succ, Ex.mul_b, ih]

theorem Ex.mul_const (p : Ex h c) (x : U) : p * ⟨1, x⟩ = ⟨p.b, p.u * x⟩ :=
  Ex.ext (by show p.b * 1 = p.b; exact _root_.mul_one _)
    (by show p.u * x * (θ c p.b 1)⁻¹ = p.u * x; rw [h.face₃, inv_one, _root_.mul_one])

theorem Ex.const_pow (x : U) (n : ℕ) : (⟨1, x⟩ : Ex h c) ^ n = ⟨1, x ^ n⟩ := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ n ih => rw [pow_succ, ih, Ex.mul_const, pow_succ]

variable {X : Type} [AddCommGroup X]

def Mult (θ : A → A → A → U) (c : X → A) (b : A) (v : X → U) : Prop :=
  v 0 = 1 ∧ ∀ χ χ', v (χ + χ') * θ (c χ) (c χ') b = v χ * v χ'

private theorem isCub_theta_mul_left_relation (h : IsCub θ) (c c' b₁ b₂ : A) :
    θ c b₁ b₂ * θ c' b₁ b₂ * θ c c' (b₁ * b₂) = θ c c' b₁ * θ c c' b₂ * θ (c * c') b₁ b₂ := by
  have e1 := h.coc c c' b₁ b₂
  have e2 := h.coc c' b₁ b₂ c
  rw [h.s01 c (c' * b₁) b₂, h.s12 (c' * b₁) c b₂] at e1
  rw [h.s12 c' b₁ c, h.s01 c' c b₁, h.s12 c' (b₁ * b₂) c, h.s01 c' c (b₁ * b₂), h.s12 b₁ b₂ c,
    h.s01 b₁ c b₂] at e2
  apply Additive.ofMul.injective
  have e1' := congrArg Additive.ofMul e1
  have e2' := congrArg Additive.ofMul e2
  simp only [ofMul_mul] at e1' e2' ⊢
  linear_combination (norm := abel) -e1' - e2'

private theorem mul_inv_mul_eq_mul_inv_mul_of_factorizations {G : Type} [CommGroup G] (a' v' t s a v t₁ b w t₂ p q : G) (e : a' * p = a * b)
    (m : v' * q = v * w) (k : t₁ * t₂ * s = p * q * t) : a' * v' * t⁻¹ * s = a * v * t₁⁻¹ * (b * w * t₂⁻¹) := by
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  have m' := congrArg Additive.ofMul m
  have k' := congrArg Additive.ofMul k
  simp only [ofMul_mul, ofMul_inv] at e' m' k' ⊢
  linear_combination (norm := abel) e' + m' + k'

theorem Mult.pow {c : X → A} (hc : ∀ χ χ', c (χ + χ') = c χ * c χ') {b : A} {v : X → U} (m : Mult θ c b v) (n : ℕ) :
    Mult θ c (b ^ n) fun χ => ((⟨b, v χ⟩ : Ex h (c χ)) ^ n).u := by
  obtain ⟨m0, m2⟩ := m
  have hc0 : c 0 = 1 := by simpa using (hc 0 0).symm
  have z : ∀ k : ℕ, ((⟨b, v 0⟩ : Ex h (c 0)) ^ k).u = 1 := by
    intro k
    induction k with
    | zero => rw [pow_zero]; rfl
    | succ k ih =>
      have t : θ (c 0) (b ^ k) b = 1 := by rw [hc0]; exact h.face _ _
      rw [pow_succ, Ex.mul_u, Ex.pow_b, ih]
      show 1 * v 0 * (θ (c 0) (b ^ k) b)⁻¹ = 1
      rw [t, m0]; simp
  have main : ∀ k : ℕ, ∀ χ χ', ((⟨b, v (χ + χ')⟩ : Ex h (c (χ + χ'))) ^ k).u * θ (c χ) (c χ') (b ^ k) =
      ((⟨b, v χ⟩ : Ex h (c χ)) ^ k).u * ((⟨b, v χ'⟩ : Ex h (c χ')) ^ k).u := by
    intro k
    induction k with
    | zero =>
      intro χ χ'
      rw [pow_zero, pow_zero, pow_zero, pow_zero, h.face₃]
      rfl
    | succ k ih =>
      intro χ χ'
      have key := isCub_theta_mul_left_relation h (c χ) (c χ') (b ^ k) b
      rw [← hc] at key
      rw [pow_succ, pow_succ, pow_succ, pow_succ, Ex.mul_u, Ex.mul_u, Ex.mul_u, Ex.pow_b, Ex.pow_b, Ex.pow_b]
      exact mul_inv_mul_eq_mul_inv_mul_of_factorizations _ _ _ _ _ _ _ _ _ _ _ _ (ih χ χ') (m2 χ χ') key
  exact And.intro (z n) (fun χ χ' => main n χ χ')

theorem exists_mult [Module.Free ℤ X] (h : IsCub θ) {c : X → A} (hc : ∀ χ χ', c (χ + χ') = c χ * c χ') (b : A) :
    ∃ v, Mult θ c b v := by
  let P : Additive (Ex h b) →+ Additive A :=
    MonoidHom.toAdditive (MonoidHom.mk' (fun p : Ex h b => p.b) Ex.mul_b)
  let C : X →+ Additive A := AddMonoidHom.mk' (fun χ => Additive.ofMul (c χ)) (fun χ χ' => by rw [hc]; rfl)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property P.toIntLinearMap C.toIntLinearMap
    (fun a => ⟨Additive.ofMul (⟨Additive.toMul a, 1⟩ : Ex h b), rfl⟩)
  have hb : ∀ χ, (Additive.toMul (s χ)).b = c χ := fun χ => LinearMap.congr_fun hs χ
  refine ⟨fun χ => (Additive.toMul (s χ)).u, ?_, ?_⟩
  · show (Additive.toMul (s 0)).u = 1
    rw [map_zero]; rfl
  · intro χ χ'
    show (Additive.toMul (s (χ + χ'))).u * θ (c χ) (c χ') b = (Additive.toMul (s χ)).u * (Additive.toMul (s χ')).u
    rw [map_add, toMul_add, Ex.mul_u, hb, hb, h.s01 b, h.s12 (c χ) b, inv_mul_cancel_right]

theorem exists_root [Module.Free ℤ X] {n : ℕ} (hU : ∀ u : U, ∃ r, r ^ n = u) (l : X → U) (hl : ∀ χ χ', l (χ + χ') = l χ * l χ') :
    ∃ ro : X → U, (∀ χ χ', ro (χ + χ') = ro χ * ro χ') ∧ ∀ χ, ro χ ^ n = l χ := by
  let P : Additive U →+ Additive U := MonoidHom.toAdditive (powMonoidHom n)
  let L : X →+ Additive U := AddMonoidHom.mk' (fun χ => Additive.ofMul (l χ)) (fun χ χ' => by rw [hl]; rfl)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property P.toIntLinearMap L.toIntLinearMap
    (fun a => by obtain ⟨r, hr⟩ := hU (Additive.toMul a); exact ⟨Additive.ofMul r, hr⟩)
  refine ⟨fun χ => Additive.toMul (s χ), fun χ χ' => ?_, fun χ => LinearMap.congr_fun hs χ⟩
  show Additive.toMul (s (χ + χ')) = Additive.toMul (s χ) * Additive.toMul (s χ')
  rw [map_add, toMul_add]

end Ext

section Pt

variable {F : Type} [Field F] {X : Scheme.{0}} {M : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_pt (hM : M.IsLB) {φ : K → (Sp F ⟶ X)} {ε : K → ℤ} {φ' : K' → (Sp F ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    {t : LB.Gen (LB.LinComb M φ ε)} {t' : LB.Gen (LB.LinComb M φ' ε')} (ht : t.IsGen) (ht' : t'.IsGen) {y : Sp F} {J}
    (hJ : Good M y J) (e : val t (𝟙 _) y J = val t' (𝟙 _) y J) : LB.Gen.Corr M _ _ _ _ t t' :=
  corr_of_val hM fun y' I hI => by
    have : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
    obtain rfl := Subsingleton.elim y y'
    exact (gen_trans ht (𝟙 _) y (hI.mem _ _) (hJ.mem _ _)).trans ((congrArg₂ (· * ·)
      (hF.trF (𝟙 _) y (fun ψ => I (𝟙 _ ≫ ψ)) fun ψ => J (𝟙 _ ≫ ψ)) e).trans
      (gen_trans ht' (𝟙 _) y (hI.mem _ _) (hJ.mem _ _)).symm)

theorem toStk_surj (y : Sp F) : Function.Surjective (toStk y) := by
  intro t
  obtain ⟨V, hyV, s, rfl⟩ := TopCat.Presheaf.germ_exist (Sp F).presheaf t
  have hV : (⊤ : (Sp F).Opens) ≤ V := by
    intro x _
    have hx : x = y := by
      let x' : PrimeSpectrum F := x
      let y' : PrimeSpectrum F := y
      have e : x' = y' := PrimeSpectrum.ext ((Ideal.eq_bot_of_prime x'.asIdeal).trans (Ideal.eq_bot_of_prime y'.asIdeal).symm)
      exact e
    exact hx ▸ hyV
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom ((Sp F).presheaf.map (homOfLE hV).op s), ?_⟩
  simp only [toStk]
  simp
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE hV) y trivial s

theorem exists_gen_val (hM : M.IsLB) (φ : K → (Sp F ⟶ X)) (ε : K → ℤ) {y : Sp F} {J} (hJ : Good M y J)
    (u : ((Sp F).presheaf.stalk y)ˣ) : ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧ val t (𝟙 _) y J = u := by
  have all : ∀ w : Sp F, w ∈ LB.wchart M φ fun k => J (𝟙 _ ≫ φ k) := fun w =>
    (top_le_iff_mem (𝟙 (Sp F)) _ y).2 (hJ.mem φ (𝟙 _)) trivial
  have le : ∀ j, LB.wchart M φ j ≤ LB.wchart M φ j ⊓ LB.wchart M φ fun k => J (𝟙 _ ≫ φ k) := fun j w hw => ⟨hw, all w⟩
  let t₀ : LB.Gen (LB.LinComb M φ ε) := ⟨fun j => res (le j) ((LB.LinComb M φ ε).g j fun k => J (𝟙 _ ≫ φ k))⟩
  have h₀ : t₀.IsGen := isGen_of_gm _ fun w j j' h h' =>
    ((gm_res _ w (le j) h _).trans (gm_linComb M _ ε (𝟙 _) w j _ h (all w))).trans
      ((trF_trans hM _ ε (𝟙 _) w h h' (all w)).symm.trans (congrArg _
        ((gm_res _ w (le j') h' _).trans (gm_linComb M _ ε (𝟙 _) w j' _ h' (all w))).symm))
  obtain ⟨f, hf⟩ := toStk_surj y (u * (val t₀ (𝟙 _) y J)⁻¹).val
  have f0 : f ≠ 0 := fun h => Units.ne_zero _ (hf.symm.trans (by rw [h, map_zero]))
  refine ⟨scaleGen t₀ (cU f f0), scaleGen_isGen hM t₀ h₀ _, (gm_scaleGen t₀ _ (𝟙 _) y _ (all y)).trans ?_⟩
  rw [show gm (𝟙 (Sp F)) y ⊤ (cU f f0) = _ from Units.ext ((gm_cU f f0 y).trans hf)]
  exact inv_mul_cancel_right _ _

end Pt

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

section Fwd

variable {T : Over (Sp R)} (σ : T ⟶ TF (R := R) F) {y : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L y J)

def gx (g : GtPtF D F) (χ : D.X) : Ex (isCub_cubV D.cub (T := T) hJ) (cP D T χ) := ⟨σ ≫ g.b, val (g.s χ) σ.left y J⟩

def ix (z χ : D.X) : Ex (isCub_cubV D.cub (T := T) hJ) (cP D T χ) :=
  ⟨cP D T z, val (D.tau z χ) (σ.left ≫ jFK (R := R) F) y J⟩

theorem ix_add (hB : D.TauBimult) (z z' χ : D.X) : ix σ hJ (z + z') χ = ix σ hJ z χ * ix σ hJ z' χ :=
  Ex.ext (cPoint_add _ _ _ _) (by
    have C := isCub_cubV D.cub (T := T) hJ
    exact eq_mul_inv_of_mul_eq ((congrArg _ ((C.s01 _ _ _).trans (C.s12 _ _ _))).trans (tau_mul σ hJ hB z z' χ)))

theorem gx_add {g g' g'' : GtPtF D F} (h : g.IsAdd g' g'') (χ : D.X) : gx σ hJ g'' χ = gx σ hJ g χ * gx σ hJ g' χ := by
  refine Ex.ext ((congrArg (σ ≫ ·) h.1).trans (MonObj.comp_mul _ _ _)) (eq_mul_inv_of_mul_eq ?_)
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h.2 χ) σ.left).trans (val_mul hJ _ _ _))
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) e
  exact ((val_cub D.cub σ hJ _ _ _).trans (congrArg (fun c => cubV D.cub y J c _ _) (comp_cP D σ χ))).symm

theorem gx_iota {z : D.X} {g : GtPtF D F} (h : GtPtF.IsIota z g) (χ : D.X) : gx σ hJ g χ = ix σ hJ z χ :=
  Ex.ext ((congrArg (σ ≫ ·) h.1).trans (comp_cP D σ z)) ((val_corr hJ (h.2 χ) σ.left).trans (val_pull hJ _ _ _))

theorem gx_qk {n : ℕ} (q : QkPt D F n) (χ : D.X) : gx σ hJ q.g χ ^ n = ix σ hJ q.y χ := by
  obtain ⟨h, ⟨gs, g₀, st, rfl⟩, hi⟩ := q.eq
  have : ∀ (i : ℕ) (hi : i < n + 1), gx σ hJ (gs ⟨i, hi⟩) χ = gx σ hJ q.g χ ^ i := fun i hi => by
    induction i with
    | zero => exact Ex.ext ((congrArg (σ ≫ ·) g₀.1).trans (MonObj.comp_one σ)) ((val_corr hJ (g₀.2 χ) σ.left).trans (val_one _))
    | succ i ih => exact (gx_add σ hJ (st ⟨i, by omega⟩) χ).trans (by rw [pow_succ, ← ih (by omega)]; rfl)
  exact (this n (Nat.lt_succ_self n)).symm.trans (gx_iota σ hJ hi χ)

theorem gx_equiv {n : ℕ} {p p' : QkPt D F n} (h : QkPt.Equiv D F p p') :
    ∃ z, p'.y = p.y + n • z ∧ ∀ χ, gx σ hJ p'.g χ = gx σ hJ p.g χ * ix σ hJ z χ := by
  obtain ⟨z, hy, g, hi, ha⟩ := h
  exact ⟨z, hy, fun χ => by rw [gx_add σ hJ ha, gx_iota σ hJ hi]⟩

include hJ in
theorem mult_gx (g : GtPtF D F) : Mult (th D y J) (cP D T) (σ ≫ g.b) fun χ => val (g.s χ) σ.left y J :=
  ⟨(val_corr hJ g.s_zero _).trans (val_one _), gt_mul σ hJ g⟩

end Fwd

variable {y : (TF (R := R) F).left} {J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L y J)
include hJ

theorem exists_gt_pt (b : TF (R := R) F ⟶ D.P.A) (v : D.X → _) (m : Mult (th D y J) (cP D _) b v) :
    ∃ g : GtPtF D F, g.b = b ∧ ∀ χ, val (g.s χ) (𝟙 _) y J = v χ := by
  choose s hs hv using fun χ => exists_gen_val D.P.isLB (DegPre.gtφ D F b χ) DegPre.gtε hJ (v χ)
  refine ⟨⟨b, s, hs, corr_pt D.P.isLB (fun U _ h => ?_) (hs 0) (fun i j => (map_one _).trans ((congrArg₂ (· * ·)
    (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm) hJ ((hv 0).trans (m.1.trans (val_one _).symm)),
    fun χ χ' => corr_pt D.P.isLB (fun U _ h => ?_)
      (mulGen_isGen _ _ _ _ _ _ _ (hs _) (pullGen_isGen _ _ _ _ D.cub.isGen _)) (mulGen_isGen _ _ _ _ _ _ _ (hs _) (hs _)) hJ
      (((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _) (val_cubAt hJ _ _ _))).trans ((m.2 χ χ').trans
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _) (hv _))).symm))⟩, rfl, hv⟩
  · rw [prod_gt, cPoint_zero, _root_.one_mul]; simp
  · refine (prod_sum₂ (K := Fin 4) (K' := thK.{0}) (U := U) _ (prod_gt b _ h) (prod_cub (cP D _ χ) (cP D _ χ') b h)).trans
      (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_gt b χ h) (prod_gt b χ' h)).symm)
    rw [cPoint_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem exists_qk {n : ℕ} (z : D.X) (b : TF (R := R) F ⟶ D.P.A) (v : D.X → _) (m : Mult (th D y J) (cP D _) b v)
    (hn : ∀ χ, (⟨b, v χ⟩ : Ex (isCub_cubV D.cub (T := TF (R := R) F) hJ) (cP D _ χ)) ^ n = ix (𝟙 _) hJ z χ) :
    ∃ q : QkPt D F n, q.y = z ∧ q.g.b = b ∧ ∀ χ, val (q.g.s χ) (𝟙 _) y J = v χ := by
  have C := isCub_cubV D.cub (T := TF (R := R) F) hJ
  obtain ⟨g, hb, hv⟩ := exists_gt_pt hJ b v m
  choose gs gb gv using fun i : ℕ => exists_gt_pt hJ _ _ (m.pow (h := C) (cPoint_add D _) i)
  refine ⟨⟨z, g, gs n, ⟨fun i => gs i, ⟨(gb 0).trans (pow_zero b), fun χ => corr_pt D.P.isLB (fun U _ h => ?_) ((gs 0).isGen χ)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm) hJ
    ((gv 0 χ).trans (val_one _).symm)⟩, fun i => ?_, rfl⟩, ?_⟩, rfl, hb, hv⟩
  · show ∏ i, h (DegPre.gtφ D F (gs 0).b χ i) ^ DegPre.gtε i = _
    rw [prod_gt, gb, pow_zero, _root_.mul_one]; simp
  · have e : (gs (i + 1)).b = (gs i).b * g.b := by rw [gb, gb, hb, pow_succ]
    refine ⟨e, fun χ => corr_pt D.P.isLB (fun U _ h => ?_)
      (mulGen_isGen _ _ _ _ _ _ _ ((gs _).isGen χ) (pullGen_isGen _ _ _ _ D.cub.isGen _))
      (mulGen_isGen _ _ _ _ _ _ _ ((gs _).isGen χ) (g.isGen χ)) hJ
      (((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (gv (i + 1) χ) (val_cubAt hJ _ _ _))).trans (Eq.trans ?_
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (gv i χ) (hv χ))).symm))⟩
    · refine (prod_sum₂ (K := Fin 4) (K' := thK.{0}) (U := U) _ (prod_gt (gs (i + 1)).b χ h)
        (prod_cub (cP D _ χ) (gs i).b g.b h)).trans (Eq.trans ?_
        (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_gt (gs i).b χ h) (prod_gt g.b χ h)).symm)
      rw [e, _root_.mul_assoc (cP D _ χ)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · show _ * th D y J (cP D _ χ) (gs i).b g.b = _
      rw [pow_succ, Ex.mul_u, Ex.pow_b, gb, hb, inv_mul_cancel_right]
  · have e : (gs n).b = cP D _ z := (gb n).trans ((Ex.pow_b (h := C) ⟨b, v 0⟩ n).symm.trans (congrArg Ex.b (hn 0)))
    refine ⟨e, fun χ => corr_pt D.P.isLB (fun U _ h => ?_) ((gs n).isGen χ) (pullGen_isGen _ _ _ _
      (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _)
        (invGen_isGen _ _ _ _ (D.psi_gen _))) (invGen_isGen _ _ _ _ (D.psi_gen _)))
        (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _))) _) hJ
      ((gv n χ).trans ((congrArg Ex.u (hn χ)).trans (val_pull hJ _ _ _).symm))⟩
    have a : ∀ x, jFK (R := R) F ≫ ptK (D.c x) = (cP D (TF (R := R) F) x).left := fun x => (Category.assoc _ _ _).symm
    have a₀ : jFK (R := R) F ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left :=
      (Category.assoc _ _ _).symm
    rw [prod_gt, e]
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a, a₀, cPoint_add, neg_neg, zpow_neg,
      zpow_one, mul_comm (cP D _ z)]
    ac_rfl

theorem exists_qk_over [IsAlgClosed F] (hB : D.TauBimult) {n : ℕ} (hn : 0 < n) (z : D.X) (b : TF (R := R) F ⟶ D.P.A)
    (hb : b ^ n = cP D _ z) : ∃ q : QkPt D F n, q.y = z ∧ q.g.b = b := by
  have C := isCub_cubV D.cub (T := TF (R := R) F) hJ
  obtain ⟨v, m⟩ := exists_mult C (cPoint_add D (TF (R := R) F)) b
  have mp := m.pow (h := C) (cPoint_add D _) n
  have sy := tau_symm (D := D) (𝟙 (TF (R := R) F)) hJ
  obtain ⟨ro, hro, hron⟩ := exists_root (n := n) (fun u => by
      obtain ⟨f, hf⟩ := toStk_surj (F := F) y u.val
      obtain ⟨r, rfl⟩ := IsAlgClosed.exists_pow_nat_eq f hn
      have r0 : r ≠ 0 := fun h => u.ne_zero (hf.symm.trans (by rw [h, zero_pow hn.ne', map_zero]))
      exact ⟨Units.map (toStk (F := F) y).toMonoidHom (Units.mk0 r r0), Units.ext ((map_pow (toStk (F := F) y) r n).symm.trans hf)⟩)
    (fun χ => (ix (𝟙 _) hJ z χ).u * (((⟨b, v χ⟩ : Ex C (cP D _ χ)) ^ n).u)⁻¹) fun χ χ' => by
      have a₁ := congrArg Additive.ofMul (mp.2 χ χ')
      have a₂ := congrArg Additive.ofMul (tau_mul (𝟙 (TF (R := R) F)) hJ hB χ χ' z)
      rw [hb] at a₁
      apply Additive.ofMul.injective
      simp only [ix, sy z, ofMul_mul, ofMul_inv] at a₁ a₂ ⊢
      linear_combination (norm := abel) a₂ - a₁
  have ro0 : ro 0 = 1 := mul_eq_left.1 ((hro 0 0).symm.trans (by rw [add_zero]))
  obtain ⟨q, h₁, h₂, -⟩ := exists_qk hJ (n := n) z b (fun χ => v χ * ro χ) ⟨by simp only [m.1, ro0, _root_.mul_one], fun χ χ' => by
    beta_reduce
    rw [hro, mul_right_comm, m.2, _root_.mul_mul_mul_comm]⟩ fun χ => by
      rw [← Ex.mul_const (h := C) ⟨b, v χ⟩, mul_pow, Ex.const_pow, Ex.mul_const, hron]
      exact Ex.ext ((Ex.pow_b _ _).trans hb) (mul_mul_inv_cancel'_right _ _)
  exact ⟨q, h₁, h₂⟩

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
