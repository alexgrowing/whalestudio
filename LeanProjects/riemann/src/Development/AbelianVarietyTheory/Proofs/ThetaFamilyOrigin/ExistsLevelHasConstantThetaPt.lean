import Mathlib
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ConstantThetaDeformationZero
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStdSympZmodStatement
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ConstThetaLevel

open ThetaPtMove

theorem exists_symplectic_points (hLaw : Laws) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) {g : ℕ}
    (hg : g = P.g) (M : ℕ) (hM : (M : K) ≠ 0) (ze : Γ(Sp K, ⊤)ˣ) (hz : IsPrimitiveRoot ze M) :
    ∃ x : Fin (2 * g) → (baseOver (Sp K) ⟶ P.A), (∀ i, x i ^ M = 1) ∧
      ∀ i j, WeilIs P.A P.L M (x i) (x j) (ze ^ stdSymp g i j) := by
  subst hg
  have := P.isAb.comm
  have : IsDomain Γ(Sp K, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain K
  obtain ⟨w₁, w₂, w₃, -⟩ := hLaw.weil _ P M (baseOver (Sp K))
  let H : Subgroup (baseOver (Sp K) ⟶ P.A) := (powMonoidHom M).ker
  have hH : ∀ x : H, x.1 ^ M = 1 := fun x => x.2
  choose c hc hu using fun x y : H => w₁ x.1 y.1 (hH x) (hH y)
  have l : ∀ x x' y, c (x * x') y = c x y * c x' y := fun x x' y => (hu _ _ _ (w₂ _ _ _ _ _ (hc x y) (hc x' y))).symm
  have s : ∀ x y, c y x = (c x y)⁻¹ := fun x y => (hu _ _ _ (CommPairing.weilIs_symm P.isLB (hc x y))).symm
  let e : H →* H →* Γ(Sp K, ⊤)ˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (c x) fun y y' => by
    rw [s (y * y'), l, mul_inv, ← s, ← s]) fun x x' => MonoidHom.ext fun y => l x x' y
  obtain ⟨x, hx⟩ := T.exists_standard_symplectic_basis_of_pairing M P.g H _ ze (Nat.pos_of_ne_zero fun h => hM (by rw [h, Nat.cast_zero])) hz
    (fun x => Subtype.ext (hH x)) (fun d hd => by
      obtain ⟨b, rfl⟩ := hd
      have hd : (d : K) ≠ 0 := left_ne_zero_of_mul (by rwa [Nat.cast_mul] at hM)
      refine Eq.trans (Nat.card_congr ?_) ((hLaw.mulN _ P d (Nat.pos_of_ne_zero fun h => hd (by
        rw [h, Nat.cast_zero]))).2.2.2.2 K (𝟙 _) hd)
      exact ⟨fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩, fun x => ⟨⟨x.1, show x.1 ^ (d * b) = 1 by
        rw [pow_mul, x.2, one_pow]⟩, Subtype.ext x.2⟩, fun _ => rfl, fun _ => rfl⟩)
    e (fun x => (hu _ _ _ (w₃ _ (hH x))).symm) (fun x h => Subtype.ext
      (hLaw.weilNondeg K P M hM x.1 (hH x) fun y hy => (show c x ⟨y, hy⟩ = 1 from h ⟨y, hy⟩) ▸ hc x ⟨y, hy⟩))
  exact ⟨fun i => (x i).1, fun i => hH _, fun i j => (show c (x i) (x j) = _ from hx i j) ▸ hc (x i) (x j)⟩

theorem map_linComb {S S' : Scheme.{0}} {A T : Over S} {A' T' : Over S'} [GrpObj A] [GrpObj A']
    (F : (T ⟶ A) →* (T' ⟶ A')) {r : ℕ} (y : Fin r → (T ⟶ A)) (a : Fin r → ℕ) :
    F (linComb y a) = linComb (fun i => F (y i)) a := by
  have h := map_list_prod F (List.ofFn fun i => y i ^ a i)
  rw [List.map_ofFn] at h
  exact h.trans (congrArg List.prod (congrArg List.ofFn (funext fun i => map_pow F (y i) (a i))))

theorem linComb_pow {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {r M : ℕ} {y : Fin r → (T ⟶ A)}
    (h : ∀ i, y i ^ M = 1) (a : Fin r → ℕ) : linComb y a ^ M = 1 := by
  refine List.prod_induction (fun y => y ^ M = 1) (fun x y hx hy => ?_) (one_pow _) fun y hy => ?_
  · rw [mul_pow, hx, hy, _root_.mul_one]
  · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hy
    rw [← pow_mul, Nat.mul_comm, pow_mul, h, one_pow]

theorem isThetaPt_fibre (hS : SecBaseChangeSt) {K R : Type} [Field K] [CommRing R] {fK : K →+* R} {P₀ : PolAV (Sp K)}
    {P : PolAV (Sp R)} {φ : P.A.left ⟶ P₀.A.left} (h : IsPolFibre fK P₀ P φ) {k : ℕ} {I : Type}
    {x : I → (baseOver (Sp R) ⟶ P.A)} {x₀ : I → (baseOver (Sp K) ⟶ P₀.A)}
    (hx : ∀ i, spMap fK ≫ (x₀ i).left = (x i).left ≫ φ) (hk : ∀ i, x i ^ (k ^ 2) = 1) {v₀ : I → Γ(Sp K, ⊤)}
    (H : IsThetaPt P₀ k x₀ v₀) : IsThetaPt P k x (fun i => (spMap fK).appTop.hom (v₀ i)) := by
  obtain ⟨ho, hu, H⟩ := H
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨p₀⟩ : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨V, hV, H⟩ := H p₀
  obtain rfl : V = ⊤ := eq_top_iff.2 fun q _ => by rwa [Subsingleton.elim (α := Sp K) q p₀]
  refine ⟨ho, (map_natCast (spMap fK).appTop.hom k) ▸ hu.map (spMap fK).appTop.hom, fun _ => ⟨⊤, trivial, ?_⟩⟩
  let t : Sp R ⟶ (overRes (T := baseOver (Sp K)) ⊤).left := spMap fK ≫ (Sp K).topIso.inv
  have ht : t ≫ (⊤ : (Sp K).Opens).ι = spMap fK := by
    show (spMap fK ≫ (Sp K).topIso.inv) ≫ _ = _
    rw [Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
  let σ : (overRes (T := baseOver (Sp R)) ⊤).left ⟶ (baseAt t).left := (⊤ : (Sp R).Opens).ι
  have : IsIso σ := inferInstanceAs (IsIso (Sp R).topIso.hom)
  have ht' : (σ ≫ (homAt t).left) ≫ (⊤ : (Sp K).Opens).ι = (⊤ : (Sp R).Opens).ι ≫ spMap fK :=
    (Category.assoc _ _ _).trans (congrArg (σ ≫ ·) ht)
  have Q := isThetaPtOver_move (σ ≫ (homAt t).left) h.2.1 h.2.2.symm σ (homAt t) rfl
    ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (ht'.trans (congrArg (· ≫ _) (Category.comp_id _).symm)))
    (isGenSec_pullS hS p₀ P₀ t) (x := fun i => overResι ⊤ ≫ x i)
    (fun i => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ht').trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (hx i)).trans (Category.assoc _ _ _).symm))))
    (fun i => by rw [← MonObj.comp_pow, hk, MonObj.comp_one]) H
  convert Q using 2 with i
  exact (congrArg (fun q => q.appTop.hom (v₀ i)) ht').symm

end ConstThetaLevel

end GlobalTheory
