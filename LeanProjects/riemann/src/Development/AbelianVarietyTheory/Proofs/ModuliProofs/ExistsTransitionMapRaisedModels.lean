import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OpenImmersionCompStructureEqGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteLiftComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelDescentCoefficientField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeeperLevelBaseModelFiniteOverShallowerStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.RaisedTransition

theorem mono_spMap_of_isDedFrac {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) :
    Mono (spMap β) := by
  letI := β.toAlgebra
  have := h.2.2
  have : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (nonZeroDivisors O) (S := F)
  infer_instance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isDedFrac_of_isInc (l : Level H) (S A : ℕ) (hS : 0 < S) (hA : l.A = A) (h1 : A = 1) (β : RZ H S A →+* KA l)
    (hβ : IsInc (RZ H S A).subtype (KA l).val.toRingHom β) : IsDedFrac β := by
  subst hA
  exact (GlobalTheory.BaseRing.isDedFrac_RZ E H l S 0 hS (by rw [h1, pow_zero])).2.2 β hβ

theorem j_over {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F}
    (C : Cpt c t β) : C.j ≫ C.s = c ≫ spMap β := by
  rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]

theorem div_mul_div {a b c : ℕ} (h : a ∣ b) (h' : b ∣ c) : c / b * (b / a) = c / a := by
  exact Nat.div_mul_div h' h

theorem levComp_trans {D : Datum H} {l l' l'' : Level H} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    {b : Base l B} {b' : Base l' B'} {b'' : Base l'' B''} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}
    {s'' : S'' ⟶ Sp B''} {o'' : Obj D l'' b'' s''} {o' : Obj D l' b' s'} {o : Obj D l b s} {r : S' ⟶ S} {g : S'' ⟶ S'}
    {ξ : SABMap o''.t o'.t g} {ν : SABMap o'.t o.t r} (hd : l.Dvd l') (hd' : l'.Dvd l'') (h' : LevComp o'' o' g ξ)
    (h : LevComp o' o r ν) (ν' : SABMap o''.t o.t (g ≫ r)) (e : ν'.φ = ξ.φ ≫ ν.φ) : LevComp o'' o (g ≫ r) ν' := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [← div_mul_div hd.1 hd'.1, pow_mul, e, ← Category.assoc, LevelCover.sec_pow ξ _ _ (h'.1 a), Category.assoc, h.1,
      Category.assoc]
  · rw [← div_mul_div hd.2.2 hd'.2.2, pow_mul, e, ← Category.assoc, LevelCover.sec_pow ξ _ _ (h'.2 a), Category.assoc,
      h.2, Category.assoc]

theorem exists_isTransition : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₀' : Level H) (B : BaseModel T l₀) (B' : BaseModel T l₀') (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β) (l₂ : Level H) (c₂ : Coeff l₂) (O₂ : Type) [CommRing O₂] (β₂ : O₂ →+* c₂.F) (Y₂ : Model (Xo l₂) c₂ β₂) (b : O →+* O₂), 0 < n → (∃ e, N ∣ n ^ e) → l₀.Dvd l₀' → l₀.Dvd l → l₀'.Dvd l₂ → l.Dvd l₂ → c.F ≤ c₂.F → IsDedFrac β → IsDedFrac β₂ → IsInc (c.F.val.toRingHom.comp β) (c₂.F.val.toRingHom.comp β₂) b → Raises B Y → Raises B' Y₂ → ∃ π : Y₂.X ⟶ Y.X, IsTransition Y Y₂ b π := by
  intro hext L₁ L₂ L₃ E _ _ _ H D Xo n N T hN l₀ l₀' B B' l c O _ β Y l₂ c₂ O₂ _ β₂ Y₂ b hn hNe d₀ d₁ d₂ d hc hβ hβ₂ hb
    hR hR₂
  obtain ⟨b₁, r₁, ν₁, hb₁, hl₁, ⟨a₁⟩⟩ := hR
  obtain ⟨b₂, r₂, ν₂, hb₂, hl₂, ⟨a₂⟩⟩ := hR₂
  obtain ⟨b₀, r₀, ν₀, hb₀, hl₀, ⟨a₀⟩⟩ := GlobalTheory.T.deeper_level_base_model_finite_over_shallower hext L₁ L₂ L₃ E H D Xo n N T hN l₀ l₀' B B' hn hNe d₀
  obtain ⟨k, r, ν, hr, hk, hl, -⟩ :=
    GlobalTheory.LevelMapField.exists_levelMap L₁ L₂ L₃ E H D Xo hN l l₂ c₂ Y₂.oF Y₂.m0 d

  have hkk : k = (IntermediateField.inclusion hc).toRingHom.comp (IntermediateField.inclusion c.le).toRingHom :=
    RingHom.ext fun x => Subtype.ext (hk x)
  obtain ⟨r', hr₁, hr₂⟩ : ∃ r' : (Xo l₂).XF c₂ ⟶ (Xo l).XF c, r' ≫ pullback.fst _ _ = r ∧
      r' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom :=
    ⟨pullback.lift r (pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom)
      (by rw [hr, hkk, spMap_comp, Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel Y.m0.toSABMap ν r' hr₁
  have hl' : LevComp Y₂.oF Y.oF r' ν' :=
    ⟨fun x => LevelCover.sec_cancel ν' Y.m0.toSABMap _ _ (by
        rw [hν', hl.1, ← hr₁, Category.assoc]; exact congrArg _ (Y.m0.eta x).symm),
      fun x => LevelCover.sec_cancel ν' Y.m0.toSABMap _ _ (by
        rw [hν', hl.2, ← hr₁, Category.assoc]; exact congrArg _ (Y.m0.etaA x).symm)⟩

  have hbβ : β₂.comp b = (IntermediateField.inclusion hc).toRingHom.comp β :=
    RingHom.ext fun x => Subtype.ext (hb x)
  have hinj : Function.Injective β₂ := by
    letI := β₂.toAlgebra
    have := hβ₂.2.2
    exact IsFractionRing.injective O₂ c₂.F
  have hbb : b₂.comp b₀ = b.comp b₁ := RingHom.ext fun x => hinj (Subtype.ext
    ((hb₂ (b₀ x)).trans ((hb₀ x).trans ((hb (b₁ x)).trans (hb₁ x)).symm)))

  obtain ⟨ν₃, hν₃⟩ := LevelCover.sab_comp ν₂ ν₀ rfl
  obtain ⟨ν₄, hν₄⟩ := LevelCover.sab_comp ν' ν₁ rfl
  obtain ⟨a⟩ : Nonempty ((ofModel Y₂).Above B.C (b.comp b₁) (r₂ ≫ r₀) ν₃) := by
    rw [← hbb]
    exact ⟨(GlobalTheory.Models.above_comp E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B.C B'.C (ofModel Y₂) b₀ b₂ r₀ ν₀ r₂ ν₂ ν₃
      a₀ a₂ hν₃).choose⟩

  have hred : IsReduced ((Xo l₂).XF c₂) := by
    have := (Xo l₂).smooth
    have : Smooth (Xo l₂).s := SmoothOfRelativeDimension.smooth D.dim _
    exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c₂.F _ (pullback.snd _ _)
      inferInstance).1
  have hover : (r₂ ≫ r₀) ≫ (Xo l₀).s = (r' ≫ r₁) ≫ (Xo l₀).s := by
    have hS : 0 < n * l₀.M := Nat.mul_pos hn (lt_of_lt_of_le (by norm_num) l₀.three_le)
    have := mono_spMap_of_isDedFrac (isDedFrac_of_isInc l₀ _ 1 hS B.A_one rfl _ B.β_inc)
    have q₁ : (r₂ ≫ r₀) ≫ B.C.j ≫ B.C.s = pullback.snd _ _ ≫ spMap β₂ ≫ spMap (b.comp b₁) := by
      rw [← Category.assoc, ← a.j_comm, Category.assoc, a.π_over, ← Category.assoc, j_over, Category.assoc]
    have q₂ : r₁ ≫ B.C.j ≫ B.C.s = pullback.snd _ _ ≫ spMap β ≫ spMap b₁ := by
      rw [← Category.assoc, ← a₁.j_comm, Category.assoc, a₁.π_over, ← Category.assoc, j_over, Category.assoc]
    rw [← cancel_mono (spMap B.β), Category.assoc, ← j_over B.C, q₁, Category.assoc, ← j_over B.C, Category.assoc, q₂,
      reassoc_of% hr₂, spMap_comp, ← Category.assoc (spMap β₂), ← spMap_comp, hbβ, spMap_comp, Category.assoc]
  obtain ⟨e₁, e₂⟩ := GlobalTheory.LevUniq.map_to_univ_unique L₁ L₂ L₃ E H D l₀ l₂ (Xo l₀) _ _ _ _ Y₂.oF _ _ ν₃ ν₄ hred hover
    (levComp_trans d₀ d₂ hl₂ hl₀ ν₃ hν₃) (levComp_trans d₁ d hl' hl₁ ν₄ hν₄)
  obtain ⟨h, mu, hh, -, -, hj, hφ, hf⟩ := GlobalTheory.Models.Cpt.Above.exists_lift E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    B.C (ofModel Y) (ofModel Y₂) b₁ b (IntermediateField.inclusion hc).toRingHom r₁ ν₁ a₁ r' ν' a.π a.mu a.π_over
    hβ₂ hbβ hr₂ (by rw [a.j_comm, e₁, Category.assoc]) (by rw [a.φ_comm, e₂, hν₄, Category.assoc])
  have hφ' : Y₂.m.φ ≫ mu.φ = ν'.φ ≫ Y.m.φ := hφ
  refine ⟨h, pullback.lift h Y₂.s hh, mu, r', pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, hf a.fin, hj,
    fun x => ?_, fun x => ?_⟩
  · exact (congrArg (_ ≫ ·) hφ').trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ Y.m.φ) (hl'.1 x)).trans (Category.assoc _ _ _)))
  · exact (congrArg (_ ≫ ·) hφ').trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ Y.m.φ) (hl'.2 x)).trans (Category.assoc _ _ _)))

end GlobalTheory.RaisedTransition
