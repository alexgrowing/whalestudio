import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.MemberTest

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}

theorem existsUnique_adjoint (X₁ : Setup F W i) (a : Matrix (Fin 8) (Fin 8) ℤ) :
    ∃! a' : Matrix (Fin 8) (Fin 8) ℤ, (W + W.transpose) * a' = a.transpose * (W + W.transpose) := by
  have hu : IsUnit (W + W.transpose).det := by rw [X₁.e8.2]; exact isUnit_one
  refine ⟨(W + W.transpose)⁻¹ * (a.transpose * (W + W.transpose)), Matrix.mul_nonsing_inv_cancel_left _ _ hu, fun b hb => ?_⟩
  rw [← hb, Matrix.nonsing_inv_mul_cancel_left _ _ hu]

theorem polar_adjoint {s : ℕ} (S a a' : Matrix (Fin s) (Fin s) ℤ) (h : S * a' = a.transpose * S) (y χ : Fin s → ℤ) :
    (a.mulVec y) ⬝ᵥ (S.mulVec χ) = y ⬝ᵥ (S.mulVec (a'.mulVec χ)) := by
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec y, Matrix.vecMul_transpose]

theorem exists_endU (𝔪 : UMem X₁ z₁ act V ev X t δ) (a : Matrix (Fin 8) (Fin 8) ℤ) :
    ∃ E : EndU 𝔪.U.toUnifPre, E.aA.left ≫ 𝔪.φ = 𝔪.φ ≫ (act a).left :=
  let ⟨a', h, _⟩ := existsUnique_adjoint X₁ a
  let ⟨E, hE, _⟩ := 𝔪.equiv a a' h
  ⟨E, hE⟩

theorem terms_sum (𝔪 : UMem X₁ z₁ act V ev X t δ) {x₀ : X₁.S.Gam} {C : Type} {lab : C → X₁.S.Gam}
    {T : (Fin 8 → X) → C → V} (h : 𝔪.Terms x₀ lab T) (c : C) :
    SumF (maximalIdeal V) (FractionRing V)
      (fun χ => algebraMap V (FractionRing V) (T (𝔪.e₈.symm χ) c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)
      (𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩) := by
  obtain ⟨x, fr, th, w₀, s, g', w, -, -, hth, -, hs, hc, hT⟩ := h
  have := (hc c).2.2 1 le_rfl (w c) (fun z J _ => (pow_one _).symm) (hc c).2.1 th s _ hs (hth (lab c))
  convert this using 2 with χ
  rw [hT, AddEquiv.apply_symm_apply]

theorem exists_frames (𝔪 : UMem X₁ z₁ act V ev X t δ) (a : X₁.S.Gam) :
    ∃ (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (fr : FrAt x), x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left ∧
      fr.IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl x.left z (J (x.left ≫ 𝔪.φ)) (J' x.left) * val fr (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J := by
  have hp := 𝔪.cart.1
  have e : jFK (R := V) (FractionRing V) = 𝟙 _ := Spec.map_id _
  have hw : (spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ≫ X₁.ρ.P.A.hom = jFK (R := V) (FractionRing V) ≫ spMap 𝔪.yK := by
    rw [e, Category.assoc, Over.w]; simp
  let x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A := Over.homMk (hp.lift _ _ hw) (hp.lift_snd _ _ hw)
  have hx : x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left := hp.lift_fst _ _ hw
  obtain ⟨fr, hfr, H⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_gen_move X₁.ρ.P.isLB 𝔪.A.isLB 𝔪.wl ((isGen_iff _).1 𝔪.wl_gen)
    (K := Fin 1) (fun _ => (X₁.ρ.pt a).left) (fun _ => x.left) (fun _ => 1) (spMap 𝔪.yK) (fun _ => hx) (X₁.ρ.fr a)
    (X₁.ρ.fr_tors a).2.1
  refine ⟨x, fr, hx, hfr, fun z J J' hJ hJ' => ?_⟩
  have := H _ (𝟙 _) z (fun _ => J (x.left ≫ 𝔪.φ)) (fun _ => J' x.left) (fun _ => hJ (x.left ≫ 𝔪.φ)) (fun _ => hJ' x.left)
  rw [val_of fr (𝟙 _) z J' (fun _ => J' x.left) (fun _ => by rw [Category.id_comp]),
    val_of (X₁.ρ.fr a) _ z J (fun _ => J (x.left ≫ 𝔪.φ)) (fun _ => by rw [hx])]
  simpa using this.symm

end GlobalTheory.Poinc.Sep.MemberTest
