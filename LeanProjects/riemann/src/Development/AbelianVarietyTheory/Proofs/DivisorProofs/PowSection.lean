import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.DenseGenericOfFlat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegAct

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := Spec.map_id _

theorem exists_spMap {k B : Type} [CommRing k] [CommRing B] (x : Sp k ⟶ Sp B) : ∃ β : B →+* k, x = spMap β :=
  ⟨(Spec.preimage x).hom, by rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]⟩

theorem unit_left' {S T : Scheme.{0}} {G : Over S} (x : T ⟶ S) (σ : 𝟙_ (Over S) ⟶ G) :
    (toUnit (Over.mk x) ≫ σ).left = x ≫ σ.left := by
  simp

variable {h N m : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem lev_zero (C : SiegPre h N ζ s) : C.lev 0 = 1 := by
  have := C.lev_add 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem lev_nsmul (C : SiegPre h N ζ s) (k : ℕ) (a : Fin h ⊕ Fin h → ℤ) : C.lev (k • a) = C.lev a ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero, lev_zero]
  | succ k ih => rw [succ_nsmul, C.lev_add, ih, pow_succ]

theorem lev_N_smul (C : SiegPre h N ζ s) (a : Fin h ⊕ Fin h → ℤ) : C.lev (N • a) = 1 := by
  rw [lev_nsmul, C.lev_tors]

def relabel (C : SiegPre h N ζ s) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (σ : B' →+* B)
    (hN : N ≠ 0) (hζ : ζ ^ N = 1) (hσ : σ ζ' = ζ ^ m)
    (hω : ∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N])
    (hinj : ∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b)
    (hsurj : ∀ a, ∃ a' b, T a' = a + N • b) : SiegPre h N ζ' (s ≫ spMap σ) where
  A := C.A
  ab := C.ab
  P := C.P
  isLB := C.isLB
  rig₁ := C.rig₁
  rig₂ := C.rig₂
  symm := C.symm
  lev x := C.lev (T x)
  lev_add a b := by rw [map_add, C.lev_add]
  lev_tors a := C.lev_tors _
  geom k _ _ x β z hx hz := by
    obtain ⟨β₀, hβ₀⟩ := exists_spMap (x ≫ s)
    have hb : β = β₀.comp σ := spMap_inj (by rw [← hx, ← Category.assoc, hβ₀, spMap_comp'])
    have h1 : β₀ ζ ^ N = 1 := by rw [← map_pow, hζ, map_one]
    let z₀ : kˣ := Units.ofPowEqOne (β₀ ζ) N h1 hN
    obtain ⟨g1, g2, g3⟩ := C.geom k x β₀ z₀ hβ₀ rfl
    have hzm : z = z₀ ^ m := Units.ext (by
      rw [hz, hb, RingHom.comp_apply, hσ, map_pow, Units.val_pow_eq_pow_val]; rfl)
    have hz₀ : z₀ ^ N = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h1)
    refine ⟨fun a => (g1 (T a)).trans ⟨hinj a, fun ⟨b, hb⟩ => ⟨T b, by rw [hb, map_nsmul]⟩⟩, fun g hg => ?_,
      fun a b => ?_⟩
    · obtain ⟨a, ha⟩ := g2 g hg
      obtain ⟨a', b, hab⟩ := hsurj a
      refine ⟨a', ?_⟩
      show toUnit _ ≫ C.lev (T a') = g
      rw [hab, C.lev_add, MonObj.comp_mul, lev_N_smul, MonObj.comp_one, _root_.mul_one, ha]
    · have e : z₀ ^ (2 * omegaStd (T a) (T b)) = z ^ (2 * omegaStd a b) := by
        rw [hzm, ← zpow_natCast, ← zpow_mul]
        refine zpow_eq_zpow_iff_modEq.2 (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one hz₀)) ?_)
        have := (hω a b).mul_left 2
        calc 2 * omegaStd (T a) (T b) ≡ 2 * (m * omegaStd a b) [ZMOD N] := this
          _ = m * (2 * omegaStd a b) := by ring
      have := g3 (T a) (T b)
      rw [e] at this
      exact this

section Calc

open GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
  {d d' d'' : ℕ}

def Sq (c' : SiegPre h n' ζ' s') (c : SiegPre h n ζ s) (φ : c'.A.left ⟶ c.A.left) : Prop :=
  ∃ φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left, IsSquare φ φ₂ ∧ LBIso c'.P (c.P.pull φ₂)

theorem Sq.comp {φ : c'.A.left ⟶ c.A.left} {ψ : c''.A.left ⟶ c'.A.left} (m : Sq c' c φ) (m' : Sq c'' c' ψ) :
    Sq c'' c (ψ ≫ φ) := by
  obtain ⟨φ₂, hs, hw⟩ := m
  obtain ⟨ψ₂, hs', hw'⟩ := m'
  refine ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (iso_pull ψ₂ hw)).trans
      c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (iso_pull_pull c.isLB φ₂ ψ₂)

theorem sRelBy_comp {φ : c'.A.left ⟶ c.A.left} {ψ : c''.A.left ⟶ c'.A.left} (m : SRelBy c' c d' d f φ)
    (m' : SRelBy c'' c' d'' d' f' ψ) : SRelBy c'' c d'' d (f' ≫ f) (ψ ≫ φ) := by
  obtain ⟨hφ, hs, hl⟩ := m
  obtain ⟨hψ, hs', hl'⟩ := m'
  refine ⟨hψ.comp hφ, Sq.comp (c := c) (c' := c') (c'' := c'') hs hs', fun a => ?_⟩
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

theorem pow_section {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}
    (hφ : IsGrpPullback A' A f φ) (x' : 𝟙_ (Over S') ⟶ A') (x : 𝟙_ (Over S) ⟶ A)
    (e : x'.left ≫ φ = f ≫ x.left) (k : ℕ) : (x' ^ k).left ≫ φ = f ≫ (x ^ k).left := by
  have e₁ : x' = SiegelPull.secPull hφ x := by
    refine push_injective hφ _ (Over.OverMorphism.ext ?_)
    exact e.trans (SiegelPull.secPull_left hφ x).symm
  have e₂ : x' ^ k = SiegelPull.secPull hφ (x ^ k) := push_injective hφ _ (by
    rw [map_pow, e₁, push_secPull', push_secPull', MonObj.comp_pow])
  rw [e₂, SiegelPull.secPull_left]

end Calc

section Twist

variable {h n N : ℕ}

structure Twist (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N)
    (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (m : ℕ) (σ : cycAway N →+* cycAway N) (f : F.X ⟶ F.X) :
    Prop where
  cop : m.Coprime N
  root : σ (zetaAway N) = zetaAway N ^ m
  fix : σ.comp j = j
  symp : ∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]
  low : ∀ x, F.univ.lev (T x) ^ (N / n) = F.univ.lev x ^ (N / n)
  comm : f ≫ F.s = F.s ≫ spMap σ
  map : ∃ ν : F.univ.A.left ⟶ F.univ.A.left, IsGrpPullback F.univ.A F.univ.A f ν ∧ Sq F.univ F.univ ν ∧
    ∀ x, (F.univ.lev (T x)).left ≫ ν = f ≫ (F.univ.lev x).left

end Twist

end GlobalTheory.SiegAct
