import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFanOrderIdealGluedClopenPieces
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}

def UValThru (Xo : Moduli D l) (c : Coeff l) {S T : Scheme.{0}} (i : Xo.XF c ⟶ T) (π : S ⟶ T) (A : Set S)
    (φ : InvFun (𝓞 E)) (J : S.IdealSheafData) (d : ℕ) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ →
    ∀ (χ : Sp W ⟶ S) (y : Sp (FractionRing W) ⟶ Xo.XF c), y ≫ i = jK W ≫ χ ≫ π → χ (closedPoint W) ∈ A →
    ∀ (t : SAB H (Sp W)) (tK : SAB H (Sp (FractionRing W))), Nonempty (SABMap tK t (jK W)) →
      Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∀ P : PELUnif (maximalIdeal W) t,
      ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] →
        ∃ n : ℕ, (n : ℝ) = d * φ.evalZ be ∧ idlAlong J χ = Ideal.span {ϖ ^ n}

variable {Xo : Moduli D l} {c : Coeff l}

theorem uValThru_top_of_disjoint {S : Scheme.{0}} {i : Xo.XF c ⟶ S} {A : Set S} (hA : IsOpen A)
    (hd : A ∩ Set.range i = ∅) (φ : InvFun (𝓞 E)) (d : ℕ) : UValThru Xo c i (𝟙 S) A φ ⊤ d := by
  intro W _ _ _ _ ϖ _ χ y hy hA' _ _ _ _ _ _ _ _
  exfalso
  let g : Sp (FractionRing W) := closedPoint (FractionRing W)
  have hsp : (jK W) g ⤳ closedPoint W := IsLocalRing.specializes_closedPoint _
  have hmem : χ ((jK W) g) ∈ A := (hsp.map χ.continuous).mem_open hA hA'
  have hrange : χ ((jK W) g) ∈ Set.range i := ⟨y g, by
    have := congrArg (fun f => f.base g) hy
    simpa using this⟩
  have : χ ((jK W) g) ∈ A ∩ Set.range i := ⟨hmem, hrange⟩
  rw [hd] at this
  exact this

theorem exists_uValOn_of_pieces {S : Scheme.{0}} (i : Xo.XF c ⟶ S) (φ : InvFun (𝓞 E)) {ι : Type} [Fintype ι]
    (A : ι → Set S) (J : ι → S.IdealSheafData) (d : ι → ℕ) (huniq : ∀ x, ∃! k, x ∈ A k) (hd : ∀ k, 1 ≤ d k)
    (hsupp : ∀ k, ∀ x ∈ (J k).support, x ∈ A k ∧ x ∉ Set.range i)
    (hv : ∀ k, UValThru Xo c i (𝟙 S) (A k) φ (J k) (d k)) :
    ∃ (d' : ℕ) (J' : S.IdealSheafData), 1 ≤ d' ∧ (∀ x ∈ J'.support, x ∉ Set.range i) ∧ UValOn Xo c i φ J' d' := by
  have hdvd : ∀ k, d k ∣ ∏ k, d k := fun k => Finset.dvd_prod_of_mem (s := Finset.univ) d (Finset.mem_univ k)
  have htop : ∀ k x, x ∉ A k → FinalTheorems.stalkId (J k) x = ⊤ := fun k x hx =>
    GlobalTheory.Vanishing.stalkId_eq_top (J k) fun hs => hx (hsupp k x hs).1
  refine ⟨∏ k, d k, ∏ k, J k ^ ((∏ k, d k) / d k), ?_, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun k _ => by have := hd k; omega)
  · intro x hx
    obtain ⟨k, hk, -⟩ := huniq x
    by_cases hs : x ∈ (J k).support
    · exact (hsupp k x hs).2
    · exfalso
      refine (mem_support_iff_stalkId _ x).1 hx ?_
      rw [stalkId_prodPow, ← Ideal.one_eq_top]
      refine Finset.prod_eq_one fun k' _ => ?_
      by_cases e : k' = k
      · subst e; rw [GlobalTheory.Vanishing.stalkId_eq_top (J k') hs, ← Ideal.one_eq_top, one_pow]
      · rw [htop k' x fun h => e ((huniq x).unique h hk), ← Ideal.one_eq_top, one_pow]
  · intro W _ _ _ hW ϖ hϖ χ y hy t tK h1 h2 P be hbe hmono
    obtain ⟨k, hk, -⟩ := huniq (χ (closedPoint W))
    obtain ⟨a, ha, hJ⟩ := hv k W hW ϖ hϖ χ y (by rw [Category.comp_id]; exact hy) hk t tK h1 h2 P be hbe hmono
    refine ⟨(∏ k, d k) / d k * a, ?_, ?_⟩
    · have hd0 : (d k : ℝ) ≠ 0 := by have := hd k; positivity
      rw [Nat.cast_mul, Nat.cast_div (hdvd k) hd0, ha]
      field_simp
    · unfold idlAlong at hJ ⊢
      rw [stalkId_prodPow, Finset.prod_eq_single k, Ideal.map_pow, hJ, Ideal.span_singleton_pow, ← pow_mul, mul_comm]
      · intro k' _ e
        rw [htop k' _ fun h => e ((huniq _).unique h hk), ← Ideal.one_eq_top, one_pow]
      · intro h; exact absurd (Finset.mem_univ k) h

end GlobalTheory.UPoinc
