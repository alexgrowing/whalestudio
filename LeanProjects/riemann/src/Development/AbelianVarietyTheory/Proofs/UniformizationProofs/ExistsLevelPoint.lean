import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusCoordAdd
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitLevels
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGrpActIterateEqOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenOfIso
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.Transl

theorem exp_alg {A X : Type} [CommRing A] {N : ℕ} {Wy Wxy Wx W1 cG cB vf vw : Aˣ} {σ : A} (s : Finset X) {f : X → A}
    {ty txy g θ : X → Aˣ} (h₁ : cB * Wxy ^ N * W1 ^ N = Wy ^ N * Wx ^ N * cG) (h₂ : vw * Wx ^ N = W1 ^ N * vf)
    (h₃ : ∀ α, txy α * θ α = g α * ty α) (h₄ : Wxy.val ^ N * σ = ∑ α ∈ s, f α * (txy α).val) :
    Wy.val ^ N * (σ * (cG * vf).val) = ∑ α ∈ s, (f α * (cB * vw * g α * (θ α)⁻¹).val) * (ty α).val := by
  have key : cB * vw * Wxy ^ N = Wy ^ N * (cG * vf) := by
    apply mul_right_cancel (b := W1 ^ N)
    calc cB * vw * Wxy ^ N * W1 ^ N = vw * (cB * Wxy ^ N * W1 ^ N) := by ac_rfl
      _ = vw * (Wy ^ N * Wx ^ N * cG) := by rw [h₁]
      _ = Wy ^ N * cG * (vw * Wx ^ N) := by ac_rfl
      _ = Wy ^ N * cG * (W1 ^ N * vf) := by rw [h₂]
      _ = Wy ^ N * (cG * vf) * W1 ^ N := by ac_rfl
  have hα : ∀ α, (f α * (cB * vw * g α * (θ α)⁻¹).val) * (ty α).val =
      (cB * vw).val * (f α * (txy α).val) := by
    intro α
    have ht : txy α = g α * ty α * (θ α)⁻¹ := eq_mul_inv_of_mul_eq (h₃ α)
    have hu : cB * vw * g α * (θ α)⁻¹ * ty α = cB * vw * txy α := by rw [ht]; ac_rfl
    calc (f α * (cB * vw * g α * (θ α)⁻¹).val) * (ty α).val
        = f α * (cB * vw * g α * (θ α)⁻¹ * ty α).val := by rw [Units.val_mul _ (ty α), _root_.mul_assoc]
      _ = f α * (cB * vw * txy α).val := by rw [hu]
      _ = (cB * vw).val * (f α * (txy α).val) := by rw [Units.val_mul _ (txy α)]; ring
  rw [Finset.sum_congr rfl (fun α _ => hα α), ← Finset.mul_sum, ← h₄]
  have hv := congrArg Units.val key
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hv
  simp only [Units.val_mul]
  linear_combination (-σ) * hv

section Level
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : PreU I D A G) {T : Over (Spec (CommRingCat.of R))}
open ReciprocityTheory.ChartRestriction.G.DVR

def wv (e : ℕ) {Z : Scheme.{0}} (z : Z) (JG : (Z ⟶ G.left) → U.P.L.L.ι) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
    (a : Z ⟶ (thickObj R I e G).left) : (Z.presheaf.stalk z)ˣ :=
  gw (U.w e) a z (J (a ≫ (U.gt e).pG.left)) (fun _ => JG (a ≫ (fstG I e G).left))

def upHom (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (Z ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj Z ⟶ G) :=
  MonoidHom.mk' (fun a => (Over.map (thick R I e)).map a ≫ fstG I e G) FormalPoint.map_mul_fstG

def imHom (e : ℕ) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (Z ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj Z ⟶ D.P.A) :=
  MonoidHom.mk' (TorusCoord.im (U.gt e)) (TorusCoord.im_mul (U.gt e))

def FrameRel (x : T ⟶ G) (b : T ⟶ D.P.A) (N : ℕ)
    (f : LB.Gen (LB.LinComb U.P.L.L (K := Fin 2) ![(1 : T ⟶ G).left, x.left] ![(N : ℤ), -(N : ℤ)]))
    (w : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(1 : T ⟶ D.P.A).left, b.left] ![(N : ℤ), -(N : ℤ)])) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T.left) (o a : Z ⟶ (thickObj R I e G).left),
    o ≫ (fstG I e G).left = r ≫ (1 : T ⟶ G).left → a ≫ (fstG I e G).left = r ≫ x.left →
    ∀ (z : Z) (JG) (J), Good U.P.L.L z JG → Good D.P.L z J →
      val w r z J * wv U e z JG J a ^ N = wv U e z JG J o ^ N * val f r z JG

variable {U}

theorem exists_level_point {x : T ⟶ G} {g : GtPt D T} (hr : U.Red x g) {N : ℕ} (hx : x ^ N = 1) {e : ℕ}
    {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : (Over.map (thick R I e)).obj Z ⟶ T) :
    ∃ a : Z ⟶ thickObj R I e G, upHom I e G Z a = τ ≫ x ∧ imHom U e Z a = τ ≫ g.b ∧ a ^ N = 1 := by
  obtain ⟨a, ha⟩ := GlobalTheory.FormalPoint.exists_lift_fstG (τ ≫ x)
  have hup : upHom I e G Z a = τ ≫ x := ha
  have hleft : a.left ≫ (fstG I e G).left = τ.left ≫ x.left := by
    have := congrArg CommaMorphism.left ha
    simpa using this
  refine ⟨a, hup, ?_, ?_⟩
  · show (Over.map (thick R I e)).map a ≫ (U.gt e).pG = τ ≫ g.b
    ext1
    simpa using (hr e _ τ.left a.left hleft).1
  · apply GlobalTheory.FormalPoint.eq_of_map_fstG
    change upHom I e G Z (a ^ N) = upHom I e G Z 1
    rw [map_pow, map_one, hup, ← CategoryTheory.MonObj.comp_pow, hx, CategoryTheory.MonObj.comp_one]

theorem exists_over_point {e : ℕ} {Z : Scheme.{0}} (y₀ : Z ⟶ (thickObj R I e G).left) (rG : Z ⟶ (T ⊗ G).left)
    (rB : Z ⟶ (T ⊗ D.P.A).left) (e₁ : rG ≫ (snd T G).left = y₀ ≫ (fstG I e G).left)
    (e₂ : rB ≫ (snd T D.P.A).left = y₀ ≫ (U.gt e).pG.left) (e₃ : rB ≫ (fst T D.P.A).left = rG ≫ (fst T G).left) :
    ∃ τ : (Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ T,
      rG = (lift τ (upHom I e G _ (Over.homMk y₀ rfl))).left ∧ rB = (lift τ (imHom U e _ (Over.homMk y₀ rfl))).left := by
  have h1 : (fst T G).left ≫ T.hom = (snd T G).left ≫ G.hom := by
    rw [Over.w (fst T G), Over.w (snd T G)]
  have h2 : (fstG I e G).left ≫ G.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (fstG I e G)
  have hw : (rG ≫ (fst T G).left) ≫ T.hom = (y₀ ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    simp only [Category.assoc]
    rw [h1, reassoc_of% e₁, h2]
  have hG : rG ≫ (T ⊗ G).hom = (y₀ ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    rw [← Over.w (fst T G), ← Category.assoc]; exact hw
  have hB : rB ≫ (T ⊗ D.P.A).hom = (y₀ ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    rw [← Over.w (fst T D.P.A), ← Category.assoc, e₃]; exact hw
  refine ⟨Over.homMk (rG ≫ (fst T G).left) hw, ?_, ?_⟩
  · have key : (Over.homMk rG hG : (Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ T ⊗ G) =
        lift (Over.homMk (rG ≫ (fst T G).left) hw) (upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst]; ext1; simp
      · rw [lift_snd]
        show Over.homMk rG hG ≫ snd T G = (Over.map (thick R I e)).map (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl) ≫ fstG I e G
        ext1; simpa using e₁
    exact congrArg CommaMorphism.left key
  · have key : (Over.homMk rB hB : (Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ T ⊗ D.P.A) =
        lift (Over.homMk (rG ≫ (fst T G).left) hw) (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst]; ext1; simpa using e₃
      · rw [lift_snd]
        show Over.homMk rB hB ≫ snd T D.P.A = (Over.map (thick R I e)).map (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl) ≫ (U.gt e).pG
        ext1; simpa using e₂
    exact congrArg CommaMorphism.left key

theorem expT_transl (hG : GlobalFnsSt) {x : T ⟶ G} {g : GtPt D T} (hr : U.Red x g) {N : ℕ} (hx : x ^ N = 1)
    {f₀ w} (hf : FrameRel U x g.b N f₀ w) {σ : U.SecGT (𝟙_ _) N} {σ' : U.SecGT T N}
    {f : ∀ α, SecBT D (𝟙_ _) N α} {f' : ∀ α, SecBT D T N α}
    (hσ : ∀ (T' : Over (Spec (CommRingCat.of R))) (τ : T' ⟶ T) (y : T' ⟶ G) (z : T'.left) (J), Good U.P.L.L z J →
      sval σ' (lift τ y).left z J = sval σ (lift (toUnit T') ((τ ≫ x) * y)).left z J *
        (cubN (cubV U.P.c z J) N 1 (τ ≫ x) y * val f₀ τ.left z J).val)
    (hf' : ∀ α (T' : Over (Spec (CommRingCat.of R))) (τ : T' ⟶ T) (y : T' ⟶ D.P.A) (z : T'.left) (J),
      Good D.P.L z J → sval (f' α) (lift τ y).left z J =
        sval (f α) (lift (toUnit T') ((τ ≫ g.b) * y)).left z J * (fac g N w α τ y z J).val)
    (h : U.ExpT (𝟙_ _) N σ f) : U.ExpT T N σ' f' := by
  intro e
  obtain ⟨s, hs⟩ := h e
  refine ⟨s, ?_⟩
  intro Z y₀ rG rB e₁ e₂ e₃ z JG J hJG hJ
  obtain ⟨τ, hτG, hτB⟩ := exists_over_point (U := U) y₀ rG rB e₁ e₂ e₃
  subst hτG hτB
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_level_point hr hx τ
  have hal : a.left ≫ (fstG I e G).left = τ.left ≫ x.left := congrArg CommaMorphism.left ha₁
  have hu : (Over.map (thick R I e)).map (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) ≫ fstG I e G =
      (τ ≫ x) * upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl) := by
    rw [show (Over.map (thick R I e)).map (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) ≫ fstG I e G =
      upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) from rfl, map_mul, ha₁]
  have hi : (Over.map (thick R I e)).map (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) ≫ (U.gt e).pG =
      (τ ≫ g.b) * imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl) := by
    rw [show (Over.map (thick R I e)).map (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) ≫ (U.gt e).pG =
      imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) from rfl, map_mul, ha₂]
  have c₁ := (congrArg CommaMorphism.left (lift_snd (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ x) * upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)))).trans
    (congrArg CommaMorphism.left hu).symm
  have c₂ := (congrArg CommaMorphism.left (lift_snd (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ g.b) * imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)))).trans
    (congrArg CommaMorphism.left hi).symm
  have c₃ := (congrArg CommaMorphism.left (lift_fst (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ g.b) * imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)))).trans
    (congrArg CommaMorphism.left (lift_fst (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ x) * upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)))).symm
  obtain ⟨hz, hsum⟩ := hs Z (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)).left
    (lift (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ x) * upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl))).left
    (lift (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ g.b) * imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl))).left c₁ c₂ c₃ z JG J hJG hJ
  refine ⟨fun α hα => ?_, ?_⟩
  · rw [hf' α _ τ _ z J hJ, hz α hα, zero_mul]
  have hcube : ∀ p q u : (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ thickObj R I e G,
      @id (Z.presheaf.stalk z)ˣ (cubV (T := ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) D.cub z J (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) p) (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) q)
        (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) u)) *
          wv U e z JG J (p * q).left * wv U e z JG J (p * u).left * wv U e z JG J (q * u).left *
          wv U e z JG J (1 : (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ thickObj R I e G).left =
        wv U e z JG J (p * q * u).left * wv U e z JG J p.left * wv U e z JG J q.left * wv U e z JG J u.left *
          @id (Z.presheaf.stalk z)ˣ (cubV (T := ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) U.P.c z JG (upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) p) (upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) q)
            (upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) u)) :=
    fun p q u => (U.w_vals e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) z JG J hJG hJ (fun q => wv U e z JG J q.left) (fun _ => rfl)).2.2 p q u
  have H1 := cubN_twist (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom))) (upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom))) (fun q => wv U e z JG J q.left)
    (θ := cubV (T := ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) D.cub z J) (θ' := cubV (T := ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) U.P.c z JG) hcube ha₃ (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)
  rw [ha₁, ha₂] at H1
  have h1o : (1 : (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ thickObj R I e G).left ≫ (fstG I e G).left = τ.left ≫ (1 : T ⟶ G).left := by
    have h1 : upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) 1 = τ ≫ (1 : T ⟶ G) := by rw [map_one, MonObj.comp_one]
    exact congrArg CommaMorphism.left h1
  have H2 := hf e Z τ.left (1 : (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ thickObj R I e G).left a.left h1o hal z JG J hJG hJ
  have ha₂' : (Over.map (thick R I e)).map a ≫ (U.gt e).pG = τ ≫ g.b := ha₂
  have H3 : ∀ α, @id (Z.presheaf.stalk z)ˣ (val ((U.gt e).t α) (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)).left z J) *
      @id (Z.presheaf.stalk z)ˣ (th D z J (cP D ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom))) α) (τ ≫ g.b) (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl))) =
      @id (Z.presheaf.stalk z)ˣ (val (g.s α) τ.left z J) * @id (Z.presheaf.stalk z)ˣ (val ((U.gt e).t α) y₀ z J) := by
    intro α
    have ht := torus_coord_add hG R I D e G (U.gt e) (Over.mk (y₀ ≫ (thickObj R I e G).hom)) a (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl) α z J hJ
    rw [ha₂'] at ht
    rw [← (hr e _ τ.left a.left hal).2 α z J hJ]
    exact ht
  rw [hσ _ τ _ z JG hJG]
  simp only [hf' _ _ τ _ z J hJ]
  exact exp_alg s H1 H2 H3 hsum

end Level

end GlobalTheory.UU.Transl
end
