import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreKilled
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledFibre

theorem one_left_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let u : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    simp only [Over.mk_hom, Category.assoc]
    rw [h.1.w, ← Category.assoc, Over.w])
  have hu : u * u = u := Over.OverMorphism.ext (by
    rw [h.2 T 1 1 u u rfl rfl, _root_.mul_one]; rfl)
  have : u = 1 := mul_eq_left.1 hu
  rw [← this]
  rfl

theorem pow_left_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ f) ⟶ G)
    (hx : x₀.left = x.left ≫ φ) (n : ℕ) : (x₀ ^ n).left = (x ^ n).left ≫ φ := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact one_left_push h T
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact h.2 T _ _ _ _ ih hx

theorem comp_pow_pt {S : Scheme.{0}} {G A B : Over S} [GrpObj G] (f : A ⟶ B) (g : B ⟶ G) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

end GlobalTheory.KerKilledFibre

namespace GlobalTheory.KerKilledFibre

theorem fibreKilled_of_base : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → IsUnit ((d : ℕ) : Γ(T, ⊤)) → (∀ (T' : Over T) (x : T' ⟶ A'), (∃ s : (P'.pull (lift (snd A' T' ≫ x) (fst A' T')).left).Gen, s.IsGen) → x ^ d = 1) → ∀ t : T, GlobalTheory.KerKilledNear.FibreKilled d G P (g.base t) := by
  intro d S' _ G _ _ P _ hP _ _ _ T g A' _ _ φ φ₂ P' hpb hsq hP' hiso _ H t T' x hT' hgen
  obtain ⟨f, hf⟩ := hT'
  obtain ⟨c, hc⟩ := hgen
  let r : Spec (T.residueField t) ⟶ Spec (S'.residueField (g.base t)) := Spec.map (g.residueFieldMap t)
  have hr : r ≫ S'.fromSpecResidueField (g.base t) = T.fromSpecResidueField t ≫ g :=
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g t
  let p1 : pullback f r ⟶ T'.left := pullback.fst f r
  let p2 : pullback f r ⟶ Spec (T.residueField t) := pullback.snd f r
  let T'' : Over T := Over.mk (p2 ≫ T.fromSpecResidueField t)
  have hw : p1 ≫ T'.hom = T''.hom ≫ g := by
    show p1 ≫ T'.hom = (p2 ≫ T.fromSpecResidueField t) ≫ g
    rw [hf, ← Category.assoc, pullback.condition, Category.assoc, hr, Category.assoc]
  have hxw : (p1 ≫ x.left) ≫ G.hom = T''.hom ≫ g := by rw [Category.assoc, Over.w x]; exact hw
  let x'' : T'' ⟶ A' := Over.homMk (hpb.1.lift (p1 ≫ x.left) T''.hom hxw) (hpb.1.lift_snd _ _ _)
  have hx''φ : x''.left ≫ φ = p1 ≫ x.left := hpb.1.lift_fst _ _ _

  let Y : Over S' := Over.mk ((A' ⊗ T'').hom ≫ g)
  let a : Y ⟶ G := Over.homMk ((fst A' T'').left ≫ φ) (by
    show ((fst A' T'').left ≫ φ) ≫ G.hom = (A' ⊗ T'').hom ≫ g
    rw [Category.assoc, hpb.1.w, ← Category.assoc]
    exact congrArg (· ≫ g) (Over.w (fst A' T'')))
  let b : Y ⟶ T' := Over.homMk ((snd A' T'').left ≫ p1) (by
    show ((snd A' T'').left ≫ p1) ≫ T'.hom = (A' ⊗ T'').hom ≫ g
    rw [Category.assoc, hw, ← Category.assoc]
    exact congrArg (· ≫ g) (Over.w (snd A' T'')))
  let m := (lift a b).left
  let ψ := (lift (snd G T' ≫ x) (fst G T')).left
  let ψ'' := (lift (snd A' T'' ≫ x'') (fst A' T'')).left
  have heq : ψ'' ≫ φ₂ = m ≫ ψ := by
    have k1 : ψ ≫ (fst G G).left = (snd G T' ≫ x).left := by rw [← Over.comp_left, lift_fst]
    have k2 : ψ'' ≫ (fst A' A').left = (snd A' T'' ≫ x'').left := by rw [← Over.comp_left, lift_fst]
    have k3 : m ≫ (snd G T').left = b.left := by rw [← Over.comp_left, lift_snd]
    have k4 : ψ ≫ (snd G G).left = (fst G T').left := by rw [← Over.comp_left, lift_snd]
    have k5 : ψ'' ≫ (snd A' A').left = (fst A' T'').left := by rw [← Over.comp_left, lift_snd]
    have k6 : m ≫ (fst G T').left = a.left := by rw [← Over.comp_left, lift_fst]
    apply Over.tensorObj_ext
    · show ψ'' ≫ φ₂ ≫ (fst G G).left = m ≫ ψ ≫ (fst G G).left
      rw [hsq.1, reassoc_of% k2, k1]
      simp only [Over.comp_left, Category.assoc]
      rw [reassoc_of% k3, hx''φ]
      show _ = ((snd A' T'').left ≫ p1) ≫ x.left
      rw [Category.assoc]
    · show ψ'' ≫ φ₂ ≫ (snd G G).left = m ≫ ψ ≫ (snd G G).left
      rw [hsq.2, reassoc_of% k5, k4, k6]
      rfl
  obtain ⟨w, hwg⟩ := hiso
  obtain ⟨c1, hc1⟩ := gen_chartPull
    (chartPullSame P (fun _ : PUnit => ψ'' ≫ φ₂) (fun _ => ψ) (fun _ => 1) m (fun _ => heq)) c hc
  obtain ⟨c2, hc2⟩ := exists_down ((isGen_iff w).1 hwg) hP hP' (φ' := fun _ : PUnit => ψ'')
    (ε := fun _ => 1) c1 hc1
  have hx'' : x'' ^ d = 1 := H T'' x'' ⟨c2, hc2⟩

  let ρ : Over.mk (T''.hom ≫ g) ⟶ T' := Over.homMk p1 hw
  have hρ : (ρ ≫ x).left = x''.left ≫ φ := hx''φ.symm
  have e1 : ((ρ ≫ x) ^ d).left = (1 : Over.mk (T''.hom ≫ g) ⟶ G).left := by
    rw [pow_left_push hpb x'' (ρ ≫ x) hρ d, hx'', one_left_push hpb T'']
  have e2 : p1 ≫ (x ^ d).left = p1 ≫ (1 : T' ⟶ G).left := by
    have := congrArg CommaMorphism.left ((comp_pow_pt ρ x d).trans
      ((Over.OverMorphism.ext e1).trans (MonObj.comp_one ρ).symm))
    exact this
  have : Flat r := inferInstance
  have : Surjective r := ⟨Function.surjective_to_subsingleton _⟩
  have : Epi p1 := Flat.epi_of_flat_of_surjective _
  exact Over.OverMorphism.ext ((cancel_epi p1).1 e2)

end GlobalTheory.KerKilledFibre
