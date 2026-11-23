import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaStdAddNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegGeomLift

def baseAt {B : Type} [CommRing B] {N : ℕ} (b : TBase B N) {k : Type} [Field k] (β : B →+* k) : TBase k N where
  ζ := Units.map β.toMonoidHom b.ζ
  unit := by simpa using b.unit.map β
  prim := fun K _ β' => b.prim K (β'.comp β)

theorem exists_geom_level : ∀ (h n N : ℕ) (B : Type) [CommRing B] (b : TBase B N) (ζ₀ : B) (S : Scheme.{0}) (s : S ⟶ Sp B) (c : SiegPre h n ζ₀ s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k), 3 ≤ n → Odd N → n ∣ N → ζ₀ = (b.ζ : B) ^ (N / n) → c.Principal → x ≫ s = spMap β → ∃ e : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ c.A), (∀ a a', e (a + a') = e a * e a') ∧ (∀ a, e a ^ N = 1) ∧ (∀ a, e a ^ (N / n) = toUnit (Over.mk x) ≫ c.lev a) ∧ (∀ a, e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk x ⟶ c.A, g ^ N = 1 → ∃ a, e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N (e a) (e a') (unitOn (Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a'))) := by
  intro h n N B _ b ζ₀ S s c k _ _ x β hn ho hd hζ hc hx
  let bk := baseAt b β
  have hj : β ζ₀ = (bk.ζ : k) ^ (N / n) := by rw [hζ, map_pow]; rfl
  obtain ⟨P₁, P₂, -⟩ := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n B k ζ₀ _ β S (Sp k) s (𝟙 (Sp k)) x hj
    (by rw [hx, Category.id_comp])
  obtain ⟨c', hpb⟩ := P₁ c
  have hc' := P₂ c c' hpb hc
  obtain ⟨C, φC, pbC, ⟨φ₂C, sqC, isoC⟩, lowC⟩ := GlobalTheory.SiegLift.exists_level_lift h n N k bk c' hn ho hd hc'
  obtain ⟨φx, φ₂x, pbx, sqx, isox, levx⟩ := hpb
  let T0 : Over (Sp k) := 𝟙_ (Over (Sp k))
  have pb := IsGrpPullback.comp pbC pbx
  have wU : 𝟙 (Sp k) ≫ (T0.hom ≫ 𝟙 (Sp k) ≫ x) = x := by simp [T0]
  let U : Over.mk x ⟶ Over.mk (T0.hom ≫ 𝟙 (Sp k) ≫ x) := Over.homMk (𝟙 (Sp k)) wU
  let V : Over.mk (T0.hom ≫ 𝟙 (Sp k) ≫ x) ⟶ Over.mk x := Over.homMk (𝟙 (Sp k)) (by simp [T0])
  have VU : V ≫ U = 𝟙 _ := by ext; simp [U, V]; try rfl
  have UV : U ≫ V = 𝟙 _ := by ext; simp [U, V]; try rfl
  let ψ : (T0 ⟶ C.A) →* (Over.mk x ⟶ c.A) := (preHom U).comp (pushHom pb T0)
  have ψl : ∀ g : T0 ⟶ C.A, (ψ g).left = g.left ≫ φC ≫ φx := fun g => by
    show 𝟙 (Sp k) ≫ g.left ≫ φC ≫ φx = _
    simp
  have ψi : Function.Injective ψ := fun g g' e => by
    refine GlobalTheory.SiegelPull.push_injective pb T0 ?_
    have e' := congrArg (V ≫ ·) e
    simpa [ψ, preHom, ← Category.assoc, VU] using e'
  have ψs : Function.Surjective ψ := fun g => by
    obtain ⟨y, hy⟩ := GlobalTheory.SiegelPull.push_surjective pb T0 (V ≫ g)
    refine ⟨y, ?_⟩
    show U ≫ pushHom pb T0 y = g
    rw [hy, ← Category.assoc, UV, Category.id_comp]
  have hu : ∀ y : T0 ⟶ C.A, toUnit (Over.mk (𝟙 (Sp k))) ≫ y = y := fun y =>
    (congrArg (· ≫ y) (toUnit_unique _ (𝟙 T0))).trans (Category.id_comp _)
  obtain ⟨g₁, g₂, g₃⟩ := C.geom k (𝟙 _) (RingHom.id k) bk.ζ
    ((Category.id_comp _).trans (Spec.map_id _).symm) rfl
  simp only [hu] at g₁ g₂ g₃
  refine ⟨fun a => ψ (C.lev a), fun a a' => show ψ (C.lev (a + a')) = ψ (C.lev a) * ψ (C.lev a') by rw [C.lev_add, map_mul], fun a => show ψ (C.lev a) ^ N = 1 by rw [← map_pow, C.lev_tors, map_one],
    fun a => ?_, fun a => ?_, fun g hg => ?_, fun a a' => ?_⟩
  · apply Over.OverMorphism.ext
    rw [← map_pow, ψl, ← Category.assoc, lowC, pow_one, Category.id_comp, levx, Over.comp_left, Over.toUnit_left]
    rfl
  · rw [← map_one ψ, ψi.eq_iff]
    exact g₁ a
  · obtain ⟨y, rfl⟩ := ψs g
    obtain ⟨a, ha⟩ := g₂ y (ψi (by rw [map_pow, hg, map_one]))
    exact ⟨a, show ψ (C.lev a) = ψ y by rw [ha]⟩
  · have W1 := (GlobalTheory.weilIs_grpPullback_of_comm (Sp k) (Sp k) c'.A C.A (𝟙 (Sp k)) φC _ _ (pull_isLB c'.isLB _)
      (pull_isLB C.isLB _) pbC (GlobalTheory.SiegelPull.diag_iso sqC isoC) T0 N (C.lev a) (C.lev a')
      (pushHom pbC T0 (C.lev a)) (pushHom pbC T0 (C.lev a')) _ rfl rfl).1 (g₃ a a')
    have W2 := (GlobalTheory.weilIs_grpPullback_of_comm S (Sp k) c.A c'.A x φx _ _ (pull_isLB c.isLB _)
      (pull_isLB c'.isLB _) pbx (GlobalTheory.SiegelPull.diag_iso sqx isox) (Over.mk (T0.hom ≫ 𝟙 (Sp k))) N _ _
      (pushHom pbx _ (pushHom pbC T0 (C.lev a))) (pushHom pbx _ (pushHom pbC T0 (C.lev a'))) _ rfl rfl).1 W1
    exact GlobalTheory.SiegCover.weilIs_congr_base (by simp [T0]) ((Category.assoc _ _ _).trans (ψl _).symm)
      ((Category.assoc _ _ _).trans (ψl _).symm) W2

end GlobalTheory.SiegGeomLift
