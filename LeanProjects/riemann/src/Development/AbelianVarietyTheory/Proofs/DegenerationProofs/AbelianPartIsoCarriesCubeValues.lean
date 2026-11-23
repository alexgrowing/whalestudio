import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

noncomputable section
namespace GlobalTheory.Ex.AbPartCube

theorem exists_move {X₁ X₂ B Y : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : B ⟶ X₁} {f₂ : B ⟶ X₂}
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) (h₁ : L₁.IsLB) (h₂ : L₂.IsLB) {K : Type} [Fintype K]
    (φ' : K → (Y ⟶ B)) {φ₁ : K → (Y ⟶ X₁)} (e : ∀ k, φ' k ≫ f₁ = φ₁ k) {ε : K → ℤ}
    (t₁ : LB.Gen (LB.LinComb L₁ φ₁ ε)) (ht : t₁.IsGen) :
    ∃ t₂ : LB.Gen (LB.LinComb L₂ (fun k => φ' k ≫ f₂) ε), t₂.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J₁ J₂, Good L₁ z J₁ → Good L₂ z J₂ → val t₂ r z J₂ =
        (∏ k, gw w (r ≫ φ' k) z (J₂ ((r ≫ φ' k) ≫ f₂)) (fun _ => J₁ ((r ≫ φ' k) ≫ f₁)) ^ ε k) * val t₁ r z J₁ := by
  obtain rfl : (fun k => φ' k ≫ f₁) = φ₁ := funext e
  have le : ∀ j : K → PUnit → L₁.ι, LB.wchart (L₁.pull f₁) φ' j ≤
      LB.wchart L₁ (fun k => φ' k ≫ f₁) (fun k => j k PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun k => mem_pull (x := φ' k y).1 (Set.mem_iInter.1 hy k)
  let a : LB.Gen (LB.LinComb (L₁.pull f₁) φ' ε) := ⟨fun j => res (le j) (t₁.s fun k => j k PUnit.unit)⟩
  have ha : a.IsGen := isGen_of_gm a fun y j j' hj hj' => by
    refine (gm_res (𝟙 Y) y (le j) hj _).trans ((gen_trans ht (𝟙 Y) y (le j hj) (le j' hj')).trans
      (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_) (gm_res (𝟙 Y) y (le j') hj' _).symm))
    refine Eq.trans ?_ (gm_pull_g L₁ f₁ (𝟙 Y ≫ φ' k) y (j k) (j' k) (Set.mem_iInter.1 hj k)
      (Set.mem_iInter.1 hj' k)).symm
    rw [Category.assoc]
  obtain ⟨t, ht', hv⟩ := exists_up ((isGen_iff w).1 hw) h₂ (pull_isLB h₁ f₁) a ha
  refine ⟨t, ht', fun Z r z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  have m : r z ∈ LB.wchart (L₁.pull f₁) φ' (fun k _ => J₁ (r ≫ φ' k ≫ f₁)) :=
    Set.mem_iInter.2 fun k => mem_pull.2 (hJ₁ (r ≫ φ' k ≫ f₁))
  refine (hv Z r z _ _ (hJ₂.mem _ r) m).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_)
    (gm_res r z (le _) m _))
  rw [Category.assoc, Category.assoc]

variable {S : Scheme.{0}} {A A' T : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']

theorem prod_cub_pt {Z : Over S} (x x' y : Z ⟶ A) {U : Type} [CommGroup U] (h : (Z ⟶ A) → U) :
    ∏ I : thK, h (lift x (lift x' y) ≫ psum A (x3 A) I.down) ^ thε I =
      h (x * x' * y) * (h (x * x'))⁻¹ * (h (x * y))⁻¹ * (h (x' * y))⁻¹ * h x * h x' * h y * (h 1)⁻¹ := by
  classical
  let h' : (Z.left ⟶ A.left) → U := fun q => if hq : q ≫ A.hom = Z.hom then h (Over.homMk q hq) else 1
  have e : ∀ q : Z ⟶ A, h' q.left = h q := fun q => dif_pos (Over.w q)
  have p := prod_cub x x' y h'
  simp only [e] at p
  exact (Finset.prod_congr rfl fun I _ => congrArg (· ^ thε I) (e _).symm).trans p

theorem cubV_move (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {L : RigLB A} {L' : RigLB A'} (c : CubicalStr A L)
    (c' : CubicalStr A' L') (g : T ⊗ A ⟶ A')
    (hg : ∀ (Z : Over S) (t : Z ⟶ T) (x y : Z ⟶ A), lift t (x * y) ≫ g = (lift t x ≫ g) * (lift t y ≫ g))
    (w : LB.Iso (L.L.pull (snd T A).left) (L'.L.pull g.left)) (hw : w.IsGen) {Z : Over S} (σ : Z ⟶ T) (z : Z.left)
    {J J'} (hJ : Good L.L z J) (hJ' : Good L'.L z J') (Ω : (Z ⟶ A) → (Z.left.presheaf.stalk z)ˣ)
    (hΩ : ∀ q, Ω q = gw w (lift σ q).left z (J' (lift σ q ≫ g).left) (fun _ => J q.left)) (x y u : Z ⟶ A) :
    cubV c' z J' (lift σ x ≫ g) (lift σ y ≫ g) (lift σ u ≫ g) =
      Ω (x * y * u) * (Ω (x * y))⁻¹ * (Ω (x * u))⁻¹ * (Ω (y * u))⁻¹ * Ω x * Ω y * Ω u * (Ω 1)⁻¹ * cubV c z J x y u := by
  have g1 : ∀ (Z : Over S) (t : Z ⟶ T), lift t (1 : Z ⟶ A) ≫ g = 1 := fun Z t =>
    mul_eq_left.1 ((hg Z t 1 1).symm.trans (by rw [_root_.mul_one]))
  let Y : Over S := A ⊗ A ⊗ A ⊗ T
  let t : Y ⟶ T := snd _ _ ≫ snd _ _ ≫ snd _ _
  let x₁ : Y ⟶ A := fst _ _
  let x₂ : Y ⟶ A := snd _ _ ≫ fst _ _
  let x₃ : Y ⟶ A := snd _ _ ≫ snd _ _ ≫ fst _ _
  obtain ⟨t₂, ht₂, hv⟩ := exists_move w hw L.isLB L'.isLB
    (fun I : thK => (lift t (lift x₁ (lift x₂ x₃) ≫ psum A (x3 A) I.down)).left)
    (φ₁ := fun I => (lift x₁ (lift x₂ x₃)).left ≫ thφ A (x3 A) I)
    (fun I => by rw [← Over.comp_left, lift_snd]; rfl)
    (LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift x₁ (lift x₂ x₃)).left) (DVR.pullGen_isGen _ _ _ _ c.isGen _)
  have ev : ∀ {Z : Over S} (σ : Z ⟶ T) (z : Z.left) {J J'}, Good L.L z J → Good L'.L z J' →
      ∀ (Ω : (Z ⟶ A) → (Z.left.presheaf.stalk z)ˣ),
      (∀ q, Ω q = gw w (lift σ q).left z (J' (lift σ q ≫ g).left) (fun _ => J q.left)) → ∀ x y u : Z ⟶ A,
      val t₂ (lift x (lift y (lift u σ)) : Z ⟶ Y).left z J' =
        Ω (x * y * u) * (Ω (x * y))⁻¹ * (Ω (x * u))⁻¹ * (Ω (y * u))⁻¹ * Ω x * Ω y * Ω u * (Ω 1)⁻¹ * cubV c z J x y u ∧
      val (LB.pullGen L'.L (thφ A' (x3 A')) thε c'.t (lift (lift t x₁ ≫ g) (lift (lift t x₂ ≫ g) (lift t x₃ ≫ g))).left)
        (lift x (lift y (lift u σ)) : Z ⟶ Y).left z J' =
        cubV c' z J' (lift σ x ≫ g) (lift σ y ≫ g) (lift σ u ≫ g) := by
    intro Z σ z J J' hJ hJ' Ω hΩ x y u
    have r₀ : (lift x (lift y (lift u σ)) : Z ⟶ Y) ≫ t = σ := by simp [t, Y]
    have r₁ : (lift x (lift y (lift u σ)) : Z ⟶ Y) ≫ x₁ = x := by simp [x₁, Y]
    have r₂ : (lift x (lift y (lift u σ)) : Z ⟶ Y) ≫ x₂ = y := by simp [x₂, Y]
    have r₃ : (lift x (lift y (lift u σ)) : Z ⟶ Y) ≫ x₃ = u := by simp [x₃, Y]
    refine ⟨(hv _ _ z J J' hJ hJ').trans (congrArg₂ (· * ·) (Eq.trans (Finset.prod_congr rfl fun I _ => ?_)
      (prod_cub_pt x y u Ω)) ((val_cub c _ hJ _ _ _).trans (by rw [r₁, r₂, r₃]))), (val_cub c' _ hJ' _ _ _).trans ?_⟩
    · rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, comp_lift, r₀, ← Category.assoc, comp_lift, comp_lift,
        r₁, r₂, r₃, lift_snd, hΩ]
    · rw [comp_lift_assoc, comp_lift_assoc, comp_lift_assoc, r₀, r₁, r₂, r₃]
  have sj : Function.Surjective
      ((snd A (A ⊗ A ⊗ T)).left ≫ (snd A (A ⊗ T)).left ≫ (snd A T).left).appTop.hom :=
    surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (surj_snd hG hA _))
  have key := gen_unique' L'.isLB (fun V _ k => ?_) _ (lift 1 (lift 1 (lift 1 (𝟙 T))) : T ⟶ Y).left ?_ sj
    (DVR.pullGen_isGen L'.L (thφ A' (x3 A')) thε c'.t c'.isGen
      (lift (lift t x₁ ≫ g) (lift (lift t x₂ ≫ g) (lift t x₃ ≫ g))).left) ht₂ (fun y I' hI' => ?_) _
    (lift x (lift y (lift u σ)) : Z ⟶ Y).left z J' hJ'
  · exact (ev σ z hJ hJ' Ω hΩ x y u).2.symm.trans (key.trans (ev σ z hJ hJ' Ω hΩ x y u).1)
  · refine (prod_cub_pt x₁ x₂ x₃ (fun q => k (lift t q ≫ g).left)).trans (Eq.trans ?_ (prod_cub _ _ _ k).symm)
    simp only [hg, g1]
  · rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, lift_snd_assoc, lift_snd_assoc, lift_snd]; rfl
  · choose I hI using fun χ : T.left ⟶ A.left => exists_chart L.isLB (χ y)
    have E := ev (𝟙 T) y hI hI' _ (fun _ => rfl) 1 1 1
    have E₂ := E.2
    rw [g1, (isCub_cubV c' hI').face] at E₂
    refine E₂.trans (Eq.trans ?_ E.1.symm)
    rw [(isCub_cubV c hI).face]
    have fin : ∀ {G U : Type} [Group G] [CommGroup U] (h : G → U), 1 = h (1 * 1 * 1) * (h (1 * 1))⁻¹ * (h (1 * 1))⁻¹ *
        (h (1 * 1))⁻¹ * h 1 * h 1 * h 1 * (h 1)⁻¹ * 1 := fun h => by simp
    exact fin fun q : T ⟶ A => gw w (lift (𝟙 T) q).left y (I' (lift (𝟙 T) q ≫ g).left) (fun _ => I q.left)

theorem theta_move : GlobalFnsSt → AllIso fun {_} _ _ {_} {_} {F} _ _ {N} {N'} ν ν' {_} w f => ∀ x y u, (N'.θ (f x) (f y) (f u) : F) * wVal ν ν' w f (x * y) * wVal ν ν' w f (x * u) * wVal ν ν' w f (y * u) * wVal ν ν' w f 1 = (N.θ x y u : F) * wVal ν ν' w f (x * y * u) * wVal ν ν' w f x * wVal ν ν' w f y * wVal ν ν' w f u := by
  intro hG R _ _ D D' F _ _ N N' ν ν' φ w f hφ hw hf x y u
  obtain ⟨z⟩ : Nonempty (Sp F) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have hJ : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial
  have hJ' : Good D'.P.L z ν'.J := fun ψ => ν'.good ψ trivial
  have im : ∀ a, lift (𝟙 _) (ν.eA a) ≫ φ.hom ≫ snd _ _ = ν'.eA (f a) := fun a => by
    rw [← Category.assoc, hf a, lift_snd]
  let Ω : (TF (R := R) F ⟶ D.P.A) → ((Sp F).presheaf.stalk z)ˣ := fun q =>
    gw w (lift (𝟙 _) q).left z (ν'.J (lift (𝟙 _) q ≫ φ.hom ≫ snd _ _).left) (fun _ => ν.J q.left)
  have vw : ∀ a, toStk z (wVal ν ν' w f a) = (Ω (ν.eA a)).val := fun a => by
    have m₁ : (snd (TF (R := R) F) D.P.A).left ((lift (𝟙 _) (ν.eA a)).left z) ∈ D.P.L.U (ν.J (ν.eA a).left) := by
      exact (congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left z ∈ D.P.L.U (ν.J (ν.eA a).left))
        (lift_snd (𝟙 _) (ν.eA a))).mpr (hJ _)
    have m₂ : (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left ((lift (𝟙 _) (ν.eA a)).left z) ∈
        D'.P.L.U (ν'.J (ν'.eA (f a)).left) := by
      exact (congrArg (fun q : TF (R := R) F ⟶ D'.P.A => q.left z ∈ D'.P.L.U (ν'.J (ν'.eA (f a)).left))
        (im a)).mpr (hJ' _)
    refine (toStk_valF (lift (𝟙 (TF (R := R) F)) (ν.eA a)).left _ z (by exact ⟨mem_pull.2 m₂, mem_pull.2 m₁⟩) _).trans ?_
    simp only [Ω, im]
    rfl
  have v : toStk z (N.θ x y u : F) = (cubV D.cub (T := TF (R := R) F) z ν.J (ν.eA x) (ν.eA y) (ν.eA u)).val :=
    (congrArg (toStk z) (ν.θ_eq x y u)).trans (toStk_valF _ _ z (hJ.mem _ _) _)
  have v' : toStk z (N'.θ (f x) (f y) (f u) : F) =
      (cubV D'.cub (T := TF (R := R) F) z ν'.J (ν'.eA (f x)) (ν'.eA (f y)) (ν'.eA (f u))).val :=
    (congrArg (toStk z) (ν'.θ_eq _ _ _)).trans (toStk_valF _ _ z (hJ'.mem _ _) _)
  have key := cubV_move hG D.P.isAb D.cub D'.cub (φ.hom ≫ snd _ _) hφ.2 w hw (𝟙 (TF (R := R) F)) z hJ hJ' Ω
    (fun _ => rfl) (ν.eA x) (ν.eA y) (ν.eA u)
  rw [im, im, im] at key
  have alg : ∀ {U : Type} [CommRing U] {a b p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ : Uˣ},
      a = p₁ * p₂⁻¹ * p₃⁻¹ * p₄⁻¹ * p₅ * p₆ * p₇ * p₈⁻¹ * b →
      a.val * p₂.val * p₃.val * p₄.val * p₈.val = b.val * p₁.val * p₅.val * p₆.val * p₇.val := by
    rintro U _ a b p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ rfl
    simp only [← Units.val_mul]
    refine congrArg Units.val (Additive.ofMul.injective ?_)
    simp only [ofMul_mul, ofMul_inv]
    abel
  apply (toStk z).injective
  simp only [map_mul, vw, v, v', map_one]
  exact alg key

end GlobalTheory.Ex.AbPartCube
end
