import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPureBCId
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpHomAlgebraisationOfReductions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureEndomorphismHomLiftSquareZeroStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

namespace GlobalTheory.PureTower

open ReciprocityTheory.ChartRestriction.G.Out (thick thickTrans thickObj thickMap thickTrans_comp)

theorem exists_end {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (W : G ⟶ G) [IsMonHom W] :
    ∃ U : G' ⟶ G', IsMonHom U ∧ U.left ≫ φ = φ ≫ W.left := by
  let U : G' ⟶ G' := Over.homMk (h.1.lift (φ ≫ W.left) G'.hom (by rw [Category.assoc, Over.w, h.1.w]))
    (h.1.lift_snd _ _ _)
  have e : U.left ≫ φ = φ ≫ W.left := h.1.lift_fst _ _ _
  exact ⟨U, Out.PullGtPf.isMonHom_of_grpPullback h h W U e, e⟩

variable {T : Type} [CommRing T] (I : Ideal T)

theorem thickMap_fst (e : ℕ) (A : Over (Sp T)) :
    thickMap T I e A ≫ pullback.fst A.hom (thick T I (e + 1)) = pullback.fst A.hom (thick T I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem thickMap_hom (e : ℕ) (A : Over (Sp T)) :
    thickMap T I e A ≫ (thickObj T I (e + 1) A).hom = (thickObj T I e A).hom ≫ thickTrans T I e :=
  pullback.lift_snd _ _ _

theorem isGrpPullback_thickMap (e : ℕ) (A : Over (Sp T)) [GrpObj A] :
    IsGrpPullback (thickObj T I e A) (thickObj T I (e + 1) A) (thickTrans T I e) (thickMap T I e A) :=
  (isGrpPullback_pullback A _).cancel
    ((isGrpPullback_pullback A _).congr (thickTrans_comp T I e).symm (thickMap_fst I e A).symm) (thickMap_hom I e A)

theorem ker_factor_sq (e : ℕ) :
    RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ^ 2
      = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx hy
  rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_succ]
  exact Ideal.mul_mem_mul hx (Ideal.pow_le_self (Nat.succ_ne_zero e) hy)

variable {S : Type} [CommRing S] {G : Over (Sp S)} [GrpObj G]

theorem isGrpPullback_red {a : S →+* T} {A : Over (Sp T)} [GrpObj A] {φ : A.left ⟶ G.left}
    (h : IsGrpPullback A G (spMap a) φ) (e : ℕ) :
    IsGrpPullback (thickObj T I e A) G (spMap ((Ideal.Quotient.mk (I ^ (e + 1))).comp a))
      (pullback.fst A.hom (thick T I e) ≫ φ) :=
  ((isGrpPullback_pullback A _).comp h).congr (by rw [← Spec.map_comp]; rfl) rfl

theorem exists_end_red {a : S →+* T} {A : Over (Sp T)} [GrpObj A] {φ : A.left ⟶ G.left}
    (h : IsGrpPullback A G (spMap a) φ) (W : G ⟶ G) [IsMonHom W] :
    ∃ U : ∀ e, thickObj T I e A ⟶ thickObj T I e A, (∀ e, IsMonHom (U e)) ∧
      (∀ e, (U e).left ≫ pullback.fst A.hom (thick T I e) ≫ φ = (pullback.fst A.hom (thick T I e) ≫ φ) ≫ W.left) ∧
      ∀ e, thickMap T I e A ≫ (U (e + 1)).left = (U e).left ≫ thickMap T I e A := by
  choose U hU eU using fun e => exists_end (isGrpPullback_red I h e) W
  refine ⟨U, hU, eU, fun e => (isGrpPullback_red I h (e + 1)).1.hom_ext ?_ ?_⟩
  · rw [Category.assoc, eU, Category.assoc (U e).left, ← Category.assoc (thickMap T I e A),
      ← Category.assoc (thickMap T I e A), thickMap_fst, eU]
  · rw [Category.assoc, Over.w, Category.assoc, thickMap_hom, ← Category.assoc, Over.w]

theorem existsUnique_hom (hF : GlobalTheory.Published.FormalAlgebraisation) (hM : GlobalTheory.Published.GrothendieckMessing) {g : ℕ}
    (hG : IsAbelianScheme G) (hg : SmoothOfRelativeDimension g G.hom) (W : G ⟶ G) [IsMonHom W] {r s : S}
    (hW : IsPureBC G W r s) [IsNoetherianRing T] (hI : IsAdicComplete I T) {p : ℕ} (hp : p.Prime) (hpI : (p : T) ∈ I)
    {a b : S →+* T} (hab : ∀ x, a x - b x ∈ I) (hu : IsUnit (a r - b s)) {A B : Over (Sp T)} [GrpObj A] [GrpObj B]
    {φ : A.left ⟶ G.left} {ψ : B.left ⟶ G.left} (hA : IsGrpPullback A G (spMap a) φ)
    (hB : IsGrpPullback B G (spMap b) ψ) :
    ∃! F : A ⟶ B, IsMonHom F ∧ ∀ (X : Scheme.{0}) (x : X ⟶ A.left) (t : X ⟶ Sp (T ⧸ I ^ (0 + 1))),
      x ≫ A.hom = t ≫ thick T I 0 → x ≫ F.left ≫ ψ = x ≫ φ := by
  obtain ⟨U, hU, eU, cU⟩ := exists_end_red I hA W
  obtain ⟨V, hV, eV, cV⟩ := exists_end_red I hB W
  have rA := isGrpPullback_red I hA
  have rB := isGrpPullback_red I hB
  have e0 : (Ideal.Quotient.mk (I ^ (0 + 1))).comp a = (Ideal.Quotient.mk (I ^ (0 + 1))).comp b :=
    RingHom.ext fun x => Ideal.Quotient.eq.2 (by simpa using hab x)
  obtain ⟨f₀, hf₀, ef₀⟩ := grpPullback_iso (rA 0) ((rB 0).congr (by rw [e0]) rfl)
  let P : ℕ → Type := fun e => {f : thickObj T I e A ⟶ thickObj T I e B // IsMonHom f ∧ U e ≫ f = f ≫ V e}
  have step : ∀ (e : ℕ) (f : P e), ∃ f' : P (e + 1), thickMap T I e A ≫ f'.1.left = f.1.left ≫ thickMap T I e B ∧
      ∀ k : thickObj T I (e + 1) A ⟶ thickObj T I (e + 1) B, IsMonHom k →
        thickMap T I e A ≫ k.left = f.1.left ≫ thickMap T I e B → k = f'.1 := by
    intro e f
    have := f.2.1
    obtain ⟨k, h₁, h₂, h₃, h₄⟩ := GlobalTheory.T.pure_endomorphism_hom_lift_square_zero hM p hp _ _
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1)))
      ⟨e + 1 + 1, by
        rw [← map_natCast (Ideal.Quotient.mk (I ^ (e + 1 + 1))), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_mem_pow hpI _⟩
      (Ideal.Quotient.factor_surjective _) (ker_factor_sq I e) g g _ _ _ _ _ _
      (PolPull.isAbelianScheme_of_isGrpPullback hG (rA (e + 1)))
      ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (rA (e + 1)).1 hg)
      (PolPull.isAbelianScheme_of_isGrpPullback hG (rB (e + 1)))
      ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (rB (e + 1)).1 hg)
      (isGrpPullback_thickMap I e A) (isGrpPullback_thickMap I e B) (U (e + 1)) (V (e + 1)) (U e) (V e) (cU e) (cV e)
      _ _ _ _ (hW _ _ _ _ (rA (e + 1)) _ (eU _)) (hW _ _ _ _ (rB (e + 1)) _ (eV _))
      (by simpa using hu.map (Ideal.Quotient.mk (I ^ (e + 1 + 1)))) f.1 f.2.2
    exact ⟨⟨k, h₁, h₃⟩, h₂, h₄⟩
  choose nx h₁ h₂ using step
  have c₀ : U 0 ≫ f₀.hom = f₀.hom ≫ V 0 := Over.OverMorphism.ext ((rB 0).1.hom_ext
    (by rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, ef₀, eU, eV, ← Category.assoc f₀.hom.left,
      ef₀]) (by rw [Over.w, Over.w]))
  let f : ∀ e, P e := fun e => Nat.rec ⟨f₀.hom, hf₀, c₀⟩ nx e
  obtain ⟨F, hF₁, hF₂, hF₃⟩ := GlobalTheory.grpHom_algebraise hF.1 T I hI A B
    (PolPull.isAbelianScheme_of_isGrpPullback hG hA).proper (PolPull.isAbelianScheme_of_isGrpPullback hG hB).proper
    (fun e => thickObj T I e A) (fun e => thickObj T I e B) (fun e => thickMap T I e A) (fun e => thickMap T I e B)
    _ _ (fun e => isGrpPullback_pullback A _) (fun e => thickMap_fst I e A) (fun e => isGrpPullback_pullback B _)
    (fun e => thickMap_fst I e B) (fun e => (f e).1) (fun e => (f e).2.1) (fun e => h₁ e (f e))
  refine ⟨F, ⟨hF₁, fun X x t ht => ?_⟩, fun K ⟨hK, eK⟩ => hF₃ K fun e => ?_⟩
  · have h0 : pullback.fst A.hom (thick T I 0) ≫ F.left = f₀.hom.left ≫ pullback.fst B.hom (thick T I 0) := hF₂ 0
    rw [← pullback.lift_fst x t ht, Category.assoc, Category.assoc, ← Category.assoc _ F.left, h0, Category.assoc, ef₀]
  · have n : ∀ e, ((Over.pullback (thick T I e)).map K).left ≫ pullback.fst B.hom (thick T I e) =
        pullback.fst A.hom (thick T I e) ≫ K.left := fun e => pullback.lift_fst _ _ _
    have key : ∀ e, (Over.pullback (thick T I e)).map K = (f e).1 := by
      intro e
      induction e with
      | zero =>
        refine Over.OverMorphism.ext ((rB 0).1.hom_ext ?_ (by rw [Over.w, Over.w]))
        rw [← Category.assoc, n, Category.assoc, eK _ _ _ pullback.condition]
        exact ef₀.symm
      | succ e ih =>
        refine h₂ e (f e) _ inferInstance ?_
        rw [← ih]
        refine (isGrpPullback_pullback B (thick T I (e + 1))).1.hom_ext ?_ ?_
        · rw [Category.assoc, n, ← Category.assoc, thickMap_fst, Category.assoc, thickMap_fst, n]
        · rw [Category.assoc, Over.w, Category.assoc, thickMap_hom, thickMap_hom, ← Category.assoc, Over.w]
    rw [← key, n]

theorem exists_isGrpPullback_of_congr : GlobalTheory.Published.FormalAlgebraisation → GlobalTheory.Published.GrothendieckMessing → ∀ (S : Type) [CommRing S] (G : Over (Sp S)) [GrpObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (W : G ⟶ G) [IsMonHom W] (r s : S), IsPureBC G W r s → ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T], IsAdicComplete (IsLocalRing.maximalIdeal T) T → ∀ p : ℕ, p.Prime → (p : T) ∈ IsLocalRing.maximalIdeal T → ∀ a b : S →+* T, (∀ x, a x - b x ∈ IsLocalRing.maximalIdeal T) → IsUnit (a (r - s)) → ∀ (A : Over (Sp T)) [GrpObj A] (φ : A.left ⟶ G.left), IsGrpPullback A G (spMap a) φ → ∃ φ' : A.left ⟶ G.left, IsGrpPullback A G (spMap b) φ' ∧ ∀ x : Sp (IsLocalRing.ResidueField T) ⟶ A.left, x ≫ A.hom = spMap (IsLocalRing.residue T) → x ≫ φ = x ≫ φ' := by
  intro hF hM S _ G _ g hG hg W _ r s hW T _ _ _ hI p hp hpI a b hab hu A _ φ hA
  have hB := isGrpPullback_pullback G (spMap b)
  have hba : ∀ x, b x - a x ∈ IsLocalRing.maximalIdeal T := fun x => by
    simpa using neg_mem (hab x)
  have un : ∀ y z : T, IsUnit y → z ∈ IsLocalRing.maximalIdeal T → IsUnit (y + z) := fun y z hy hz => by
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal y).1
      (by simpa using sub_mem ((IsLocalRing.mem_maximalIdeal _).2 h) hz) hy
  rw [map_sub] at hu
  have u₁ : IsUnit (a r - b s) := by simpa using un _ _ hu (hab s)
  have u₂ : IsUnit (b r - a s) := by
    have := un _ _ hu (hba r)
    rwa [add_comm, sub_add_sub_cancel] at this
  have u₃ : IsUnit (b r - b s) := by simpa using un _ _ u₂ (hab s)
  obtain ⟨F, ⟨hF₁, hF₂⟩, -⟩ := existsUnique_hom _ hF hM hG hg W hW hI hp hpI hab u₁ hA hB
  obtain ⟨K, ⟨hK₁, hK₂⟩, -⟩ := existsUnique_hom _ hF hM hG hg W hW hI hp hpI hba u₂ hB hA
  have FK : F ≫ K = 𝟙 A := (existsUnique_hom _ hF hM hG hg W hW hI hp hpI (fun x => by simp) hu hA hA).unique
    ⟨inferInstance, fun X x t ht => by
      rw [Over.comp_left, Category.assoc, ← Category.assoc x, hK₂ _ _ t (by rw [Category.assoc, Over.w, ht]),
        Category.assoc, hF₂ _ _ t ht]⟩ ⟨inferInstance, fun X x t ht => by simp⟩
  have KF : K ≫ F = 𝟙 _ := (existsUnique_hom _ hF hM hG hg W hW hI hp hpI (fun x => by simp) u₃ hB hB).unique
    ⟨inferInstance, fun X x t ht => by
      rw [Over.comp_left, Category.assoc, ← Category.assoc x, hF₂ _ _ t (by rw [Category.assoc, Over.w, ht]),
        Category.assoc, hK₂ _ _ t ht]⟩ ⟨inferInstance, fun X x t ht => by simp⟩
  refine ⟨F.left ≫ _, ((isGrpPullback_of_iso ⟨F, K, FK, KF⟩).comp hB).congr (Category.id_comp _) rfl,
    fun x hx => (hF₂ _ x (spMap (Ideal.Quotient.lift _ (IsLocalRing.residue T) fun y hy =>
      (IsLocalRing.residue_eq_zero_iff y).2 (by simpa using hy))) ?_).symm⟩
  rw [hx, ← Spec.map_comp]
  rfl

end GlobalTheory.PureTower
