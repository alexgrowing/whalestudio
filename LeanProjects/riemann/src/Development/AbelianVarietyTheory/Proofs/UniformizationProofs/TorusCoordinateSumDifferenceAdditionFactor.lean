import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusCoordAdd
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFactorThroughCubicalEvenIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubCoordMulMulInv
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
namespace GlobalTheory.AddLevel

theorem expand_alg {S X : Type} [CommRing S] {n : ℕ} (s s₀ : Finset X) (F F' : Fin n → X → S) (σ σ' : Fin n → S)
    (p m : X → S) (θp θm r : S) (tx ty tp tm : X → Sˣ) (Wx Wy Wp Wm kL kM : Sˣ) (k u v : X → X → Sˣ)
    (hx : ∀ i, Wx.val ^ 2 * σ i = ∑ α ∈ s, F i α * (tx α).val)
    (hy : ∀ i, Wy.val ^ 2 * σ' i = ∑ α ∈ s, F' i α * (ty α).val)
    (hp : Wp.val ^ 1 * θp = ∑ a ∈ s₀, p a * (tp a).val) (hm : Wm.val ^ 1 * θm = ∑ a ∈ s₀, m a * (tm a).val)
    (hadd : ∑ i, σ i * σ' i = r * kL.val * (θp * θm))
    (hk : Wx ^ 2 * Wy ^ 2 * kL = kM * (Wp * Wm))
    (ht : ∀ a b, kM * (tp a * tm b) = k a b * (u a b * v a b)) :
    ∑ α ∈ s, ∑ β ∈ s, (∑ i, F i α * F' i β) * ((tx α).val * (ty β).val) =
      ∑ a ∈ s₀, ∑ b ∈ s₀, r * (k a b).val * (p a * m b) * ((u a b).val * (v a b).val) := by
  have hk' := congrArg Units.val hk
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hk'
  have e₁ : ∑ α ∈ s, ∑ β ∈ s, (∑ i, F i α * F' i β) * ((tx α).val * (ty β).val) =
      ∑ i, (∑ α ∈ s, F i α * (tx α).val) * (∑ β ∈ s, F' i β * (ty β).val) := by
    simp only [Finset.sum_mul_sum]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm (s := Finset.univ)]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_comm (s := Finset.univ)]
    exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun i _ => by ring
  have e₂ : ∑ a ∈ s₀, ∑ b ∈ s₀, r * (k a b).val * (p a * m b) * ((u a b).val * (v a b).val) =
      r * kM.val * ((∑ a ∈ s₀, p a * (tp a).val) * (∑ b ∈ s₀, m b * (tm b).val)) := by
    rw [Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have h := congrArg Units.val (ht a b)
    simp only [Units.val_mul] at h
    linear_combination (-(r * p a * m b)) * h
  have e₃ : ∑ i, Wx.val ^ 2 * σ i * (Wy.val ^ 2 * σ' i) = Wx.val ^ 2 * Wy.val ^ 2 * ∑ i, σ i * σ' i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e₁, e₂, ← hp, ← hm]
  simp only [← hx, ← hy]
  rw [e₃, hadd]
  linear_combination (r * θp * θm) * hk'

theorem unit_alg {U : Type} [CommGroup U] {k p m c₁ c₂ c₃ d₁ d₂ u v : U}
    (h : p * m * (c₁ * c₂ * c₃) = u * v * (d₁ * d₂)) :
    k * (p * m) = k * d₁ * d₂ * (c₁ * c₂ * c₃)⁻¹ * (u * v) := by
  rw [eq_mul_inv_of_mul_eq h]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {e : ℕ}

noncomputable def toG (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ G) :=
  MonoidHom.mk' (fun x => (Over.map (thick R I e)).map x ≫ fstG I e G) fun x y =>
    map_mul (pushHom (isGrpPullback_pullback G (thick R I e)) T) x y

noncomputable def toB (g : GtCoord I D e G) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ D.P.A) :=
  MonoidHom.mk' (fun x => (Over.map (thick R I e)).map x ≫ g.pG) (GlobalTheory.TorusCoord.im_mul g)

theorem lift_snd_left {S : Scheme.{0}} {T B : Over S} (x : T ⟶ B) :
    (lift (toUnit T) x).left ≫ (snd (𝟙_ _) B).left = x.left := by
  rw [← Over.comp_left, lift_snd]

theorem lift_fst_left {S : Scheme.{0}} {T B : Over S} (x : T ⟶ B) :
    (lift (toUnit T) x).left ≫ (fst (𝟙_ _) B).left = (toUnit T).left := by
  rw [← Over.comp_left, lift_fst]

theorem exp_at (U : PreU I D A G) {k : ℕ} {σ : U.SecGT (𝟙_ _) k} {f : ∀ α, SecBT D (𝟙_ _) k α}
    (h : U.ExpT (𝟙_ _) k σ f) (e : ℕ) : ∃ s : Finset D.X,
      ∀ (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x : T ⟶ thickObj R I e G) (z : T.left) (JG) (J),
      Good U.P.L.L z JG → Good D.P.L z J →
      (∀ α ∉ s, sval (Z := T.left) (f α) (lift (toUnit _) (toB (U.gt e) T x)).left z J = 0) ∧ ∀ s', s ⊆ s' →
      (gw (U.w e) x.left z (J (x.left ≫ (U.gt e).pG.left)) (fun _ => JG (x.left ≫ (fstG I e G).left))).val ^ k *
          sval (Z := T.left) σ (lift (toUnit _) (toG G T x)).left z JG =
        ∑ α ∈ s', sval (Z := T.left) (f α) (lift (toUnit _) (toB (U.gt e) T x)).left z J *
          (val ((U.gt e).t α) x.left z J).val := by
  obtain ⟨s, hs⟩ := h e
  refine ⟨s, fun T x z JG J hG hJ => ?_⟩
  obtain ⟨h₁, h₂⟩ := hs T.left x.left (lift (toUnit _) (toG G T x)).left (lift (toUnit _) (toB (U.gt e) T x)).left
    (lift_snd_left _) (lift_snd_left _) ((lift_fst_left _).trans (lift_fst_left _).symm) z JG J hG hJ
  refine ⟨h₁, fun s' hs' => h₂.trans (Finset.sum_subset hs' fun α _ hα => ?_)⟩
  rw [h₁ α hα, zero_mul]

theorem val_t_add (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} {z : T.left} {J}
    (hJ : Good D.P.L z J) (a b : D.X) (x : T ⟶ thickObj R I e G) :
    val (g.t (a + b)) x.left z J * @id (T.left.presheaf.stalk z)ˣ (cubV D.cub (T := (Over.map (thick R I e)).obj T) z J
      (cT D _ a) (cT D _ b) (toB g T x)) = val (g.t a) x.left z J * val (g.t b) x.left z J := by
  refine Eq.trans ?_ ((val_corr hJ (g.t_mul a b) x.left).trans (val_mul hJ _ _ _))
  refine Eq.trans ?_ (val_mul hJ _ _ _).symm
  refine congrArg (_ * ·) (Eq.trans ?_ (val_cub D.cub ((Over.map (thick R I e)).map x) hJ _ _ _).symm)
  have e₁ : ∀ c : D.X, (Over.map (thick R I e)).map x ≫ toUnit _ ≫ D.c c = cT D _ c := fun c => by
    rw [← Category.assoc, comp_toUnit]
  rw [e₁, e₁]
  rfl
end

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {e : ℕ}

theorem additionFormulaFactor_comparisonIso_value (U : PreU I D A G) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} {z : T.left} {JG} {J}
    (hG : Good U.P.L.L z JG) (hJ : Good D.P.L z J) (W : (T ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ)
    (hW : ∀ x, W x = gw (U.w e) x.left z (J (x.left ≫ (U.gt e).pG.left)) (fun _ => JG (x.left ≫ (fstG I e G).left)))
    (x y : T ⟶ thickObj R I e G) :
    W x ^ 2 * W y ^ 2 * @id (T.left.presheaf.stalk z)ˣ
        (kap0 U.P.c U.P.sym (T := (Over.map (thick R I e)).obj T) z JG (toG G T x) (toG G T y)) =
      @id (T.left.presheaf.stalk z)ˣ
        (kap0 D.cub D.sym (T := (Over.map (thick R I e)).obj T) z J (toB (U.gt e) T x) (toB (U.gt e) T y)) *
        (W (x * y) * W (x * y⁻¹)) := by
  obtain ⟨h₁, h₂, h₃⟩ := U.w_vals e T z JG J hG hJ W hW
  have h := GlobalTheory.addition_factor_through_cubical_even_iso _ _ W _ _
    (fun a b c => cubV U.P.c (T := (Over.map (thick R I e)).obj T) z JG (toG G T a) (toG G T b) (toG G T c))
    (fun a b c => cubV D.cub (T := (Over.map (thick R I e)).obj T) z J (toB (U.gt e) T a) (toB (U.gt e) T b)
      (toB (U.gt e) T c)) _ _ h₁ h₂ h₃ x y
  simp only [map_inv] at h
  exact h

theorem torusCoordinate_sum_difference_additionFactor (hGF : GlobalFnsSt) (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    {z : T.left} {J} (hJ : Good D.P.L z J) (x y : T ⟶ thickObj R I e G) (a b : D.X) :
    @id (T.left.presheaf.stalk z)ˣ
        (kap0 D.cub D.sym (T := (Over.map (thick R I e)).obj T) z J (toB g T x) (toB g T y)) *
        (val (g.t a) (x * y).left z J * val (g.t b) (x * y⁻¹).left z J) =
      @id (T.left.presheaf.stalk z)ˣ (kapV D a b (T := (Over.map (thick R I e)).obj T) z J (toB g T x) (toB g T y)) *
        (val (g.t (a + b)) x.left z J * val (g.t (a - b)) y.left z J) :=
  unit_alg (GlobalTheory.cub_coord_mul_mul_inv _ (T.left.presheaf.stalk z)ˣ D.X
    (cubV D.cub (T := (Over.map (thick R I e)).obj T) z J)
    (isCub_cubV D.cub (T := (Over.map (thick R I e)).obj T) hJ) _ (toB g T) (cT D _)
    (fun a b => (congrArg (toUnit _ ≫ ·) (D.c_add a b)).trans (MonObj.comp_mul _ _ _))
    (fun a x => val (g.t a) x.left z J) (val_t_add g hJ)
    (fun a x y => torus_coord_add hGF R I D e G g T x y a z J hJ) a b x y)

theorem at_points (hGF : GlobalFnsSt) (U : PreU I D A G) (θ : U.SecGT (𝟙_ _) 1) (f₀ : ∀ α, SecBT D (𝟙_ _) 1 α) (r : R)
    (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) (f f' : Fin n → ∀ α, SecBT D (𝟙_ _) 2 α) (hA : U.AddG θ r σ σ')
    (hθ : U.ExpT (𝟙_ _) 1 θ f₀) (hσ : ∀ i, U.ExpT (𝟙_ _) 2 (σ i) (f i) ∧ U.ExpT (𝟙_ _) 2 (σ' i) (f' i)) (e : ℕ) :
    ∃ s₀ : Finset D.X, ∀ (T' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x' y' : T' ⟶ thickObj R I e G)
      (x y : (Over.map (thick R I e)).obj T' ⟶ D.P.A), x = toB (U.gt e) T' x' → y = toB (U.gt e) T' y' →
      ∀ (z : ((Over.map (thick R I e)).obj T').left) (J), Good D.P.L z J →
      (∀ a ∉ s₀, sval (f₀ a) (lift (toUnit _) (x * y)).left z J = 0 ∧
        sval (f₀ a) (lift (toUnit _) (x * y⁻¹)).left z J = 0) ∧ ∀ s : Finset D.X, s₀ ⊆ s →
      ∑ α ∈ s, ∑ β ∈ s, (∑ i, sval (f i α) (lift (toUnit _) x).left z J * sval (f' i β) (lift (toUnit _) y).left z J) *
        ((val (Z := ((Over.map (thick R I e)).obj T').left) ((U.gt e).t α) x'.left z J).val *
          (val (Z := ((Over.map (thick R I e)).obj T').left) ((U.gt e).t β) y'.left z J).val) =
      ∑ a ∈ s₀, ∑ b ∈ s₀, gs (𝟙 _) z ⊤ (scal ((Over.map (thick R I e)).obj T').hom r) * (kapV D a b z J x y).val *
        (sval (f₀ a) (lift (toUnit _) (x * y)).left z J * sval (f₀ b) (lift (toUnit _) (x * y⁻¹)).left z J) *
        ((val (Z := ((Over.map (thick R I e)).obj T').left) ((U.gt e).t (a + b)) x'.left z J).val *
          (val (Z := ((Over.map (thick R I e)).obj T').left) ((U.gt e).t (a - b)) y'.left z J).val) := by
  classical
  obtain ⟨s₁, h₁⟩ := exp_at U hθ e
  choose s₂ h₂ using fun i => exp_at U (hσ i).1 e
  choose s₃ h₃ using fun i => exp_at U (hσ i).2 e
  obtain ⟨s₀, a₁, a₂, a₃⟩ : ∃ s₀ : Finset D.X, s₁ ⊆ s₀ ∧ (∀ i, s₂ i ⊆ s₀) ∧ ∀ i, s₃ i ⊆ s₀ :=
    ⟨s₁ ∪ (Finset.univ.biUnion s₂ ∪ Finset.univ.biUnion s₃), Finset.subset_union_left,
      fun i => ((Finset.subset_biUnion_of_mem s₂ (Finset.mem_univ i)).trans Finset.subset_union_left).trans
        Finset.subset_union_right,
      fun i => ((Finset.subset_biUnion_of_mem s₃ (Finset.mem_univ i)).trans Finset.subset_union_right).trans
        Finset.subset_union_right⟩
  refine ⟨s₀, fun T x y _ _ hx hy z J hJ => ?_⟩
  subst hx hy
  obtain ⟨JG, hG⟩ := exists_good_pt U.P.L.isLB z
  have p := h₁ T (x * y) z JG J hG hJ
  have m := h₁ T (x * y⁻¹) z JG J hG hJ
  simp only [map_mul, map_inv] at p m
  refine ⟨fun a ha => ⟨p.1 a fun h => ha (a₁ h), m.1 a fun h => ha (a₁ h)⟩, fun s hs => ?_⟩
  exact expand_alg s s₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun i => (h₂ i T x z JG J hG hJ).2 s ((a₂ i).trans hs)) (fun i => (h₃ i T y z JG J hG hJ).2 s ((a₃ i).trans hs))
    (p.2 s₀ a₁) (m.2 s₀ a₁) (hA _ (toG G T x) (toG G T y) z JG hG) (additionFormulaFactor_comparisonIso_value U hG hJ _ (fun _ => rfl) x y)
    (torusCoordinate_sum_difference_additionFactor hGF (U.gt e) hJ x y)

end

end GlobalTheory.AddLevel

theorem GlobalTheory.addition_formula_expanded_at_level : GlobalFnsSt → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (θ : U.SecGT (𝟙_ _) 1) (f₀ : ∀ α, SecBT D (𝟙_ _) 1 α) (r : V) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) (f f' : Fin n → ∀ α, SecBT D (𝟙_ _) 2 α), U.AddG θ r σ σ' → U.ExpT (𝟙_ _) 1 θ f₀ → (∀ i, U.ExpT (𝟙_ _) 2 (σ i) (f i) ∧ U.ExpT (𝟙_ _) 2 (σ' i) (f' i)) → ∀ e : ℕ, ∃ s₀ : Finset D.X, ∀ (T : Over (Spec (CommRingCat.of V))) (x y : T ⟶ D.P.A) (xe ye : T.left ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (U.gt e).pG.left = x.left → ye ≫ (U.gt e).pG.left = y.left → xe ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom = ye ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom → ∀ (z : T.left) (J), Good D.P.L z J → (∀ a ∉ s₀, sval (f₀ a) (lift (toUnit T) (x * y)).left z J = 0 ∧ sval (f₀ a) (lift (toUnit T) (x * y⁻¹)).left z J = 0) ∧ ∀ s : Finset D.X, s₀ ⊆ s → ∑ α ∈ s, ∑ β ∈ s, (∑ i, sval (f i α) (lift (toUnit T) x).left z J * sval (f' i β) (lift (toUnit T) y).left z J) * ((val ((U.gt e).t α) xe z J).val * (val ((U.gt e).t β) ye z J).val) = ∑ a ∈ s₀, ∑ b ∈ s₀, gs (𝟙 _) z ⊤ (scal T.hom r) * (kapV D a b z J x y).val * (sval (f₀ a) (lift (toUnit T) (x * y)).left z J * sval (f₀ b) (lift (toUnit T) (x * y⁻¹)).left z J) * ((val ((U.gt e).t (a + b)) xe z J).val * (val ((U.gt e).t (a - b)) ye z J).val)) := by
  intro hGF V _ _ _ _ D A G _ _ U θ f₀ r n σ σ' f f' hA hθ hσ e
  obtain ⟨s₀, H⟩ := GlobalTheory.AddLevel.at_points hGF U θ f₀ r n σ σ' f f' hA hθ hσ e
  refine ⟨s₀, fun T x y xe ye hx hy hxy => ?_⟩
  have hT : T.hom = (xe ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom) ≫ thick V (IsLocalRing.maximalIdeal V) e := by
    rw [← Over.w x, ← hx, Category.assoc, Over.w, Category.assoc]
    rfl
  obtain ⟨Z, ⟨⟨⟩⟩, h⟩ := T
  change Z ⟶ _ at xe ye
  change h = (CategoryStruct.comp (X := Z) xe (thickObj V (IsLocalRing.maximalIdeal V) e G).hom ≫
    thick V (IsLocalRing.maximalIdeal V) e : Z ⟶ _) at hT
  subst hT
  exact H (Over.mk (xe ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom)) (Over.homMk xe rfl)
    (Over.homMk ye hxy.symm) x y (Over.OverMorphism.ext hx.symm) (Over.OverMorphism.ext hy.symm)
