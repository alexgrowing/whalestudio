import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkInjectiveClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.TorUniq

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem eq_zero_of_forall_dvd {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {l : ℕ} (hl : 2 ≤ l)
    (v : X) (h : ∀ n : ℕ, ∃ z : X, v = (l ^ n) • z) : v = 0 := by
  let b := Module.Free.chooseBasis ℤ X
  refine b.repr.injective ?_
  rw [map_zero]
  ext i
  rw [Finsupp.zero_apply]
  obtain ⟨N, hN⟩ : ∃ N, N = (b.repr v i).natAbs := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ := h N
  have hd : ((l ^ N : ℕ) : ℤ) ∣ b.repr v i :=
    ⟨b.repr z i, by rw [hz, ← natCast_zsmul, map_zsmul, Finsupp.smul_apply, smul_eq_mul]⟩
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd ?_
  rw [Int.natAbs_natCast, ← hN]
  exact Nat.lt_pow_self (by omega)

theorem exists_eq_add_nsmul {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {F : Type} [Field F]
    {k : ℕ} {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ k) {u v : X}
    (h : ∀ τ : Multiplicative X →* Fˣ, τ ^ k = 1 → τ (Multiplicative.ofAdd u) = τ (Multiplicative.ofAdd v)) :
    ∃ z : X, v = u + k • z := by
  let b := Module.Free.chooseBasis ℤ X
  have key : ∀ i, ∃ c : ℤ, b.repr (v - u) i = k * c := fun i => by
    let τ : Multiplicative X →* Fˣ := (zpowersHom Fˣ ζ).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom)
    have e : ζ ^ (b.repr u i) = ζ ^ (b.repr v i) := h τ (MonoidHom.ext fun x => by
      show (ζ ^ (b.coord i x.toAdd)) ^ k = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow])
    refine (hζ.zpow_eq_one_iff_dvd _).1 ?_
    rw [map_sub, Finsupp.sub_apply, zpow_sub, e, mul_inv_cancel]
  choose c hc using key
  refine ⟨∑ i, c i • b i, ?_⟩
  rw [← sub_eq_iff_eq_add', ← b.sum_repr (v - u), Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hc, mul_smul, natCast_zsmul]

end GlobalTheory.Poinc.TorUniq

namespace GlobalTheory.Poinc.Eq8

open GlobalTheory.Poinc.TorUniq

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem torMatch_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), Function.Injective g → ∀ ρ ρ', TorMatch U U' g β ρ → TorMatch U U' g β ρ' → ρ = ρ' := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV G' _ _ hG' D' A' U' g β hg ρ ρ' h h'
  have hL := GlobalTheory.firstFiveLaws
  let gK : FractionRing R →+* FractionRing V := IsFractionRing.lift (A := R) (K := FractionRing R)
    (g := (algebraMap V (FractionRing V)).comp g) ((IsFractionRing.injective V (FractionRing V)).comp hg)
  have hgK : ∀ r, gK (algebraMap R _ r) = algebraMap V _ (g r) := IsFractionRing.lift_algebraMap _
  let F := AlgebraicClosure (FractionRing V)
  letI : Algebra (FractionRing R) F := ((algebraMap (FractionRing V) F).comp gK).toAlgebra
  have hF : ∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g r)) :=
    fun r => congrArg (algebraMap (FractionRing V) F) (hgK r)

  have img : ∀ {S : Type} [CommRing S] [IsDomain S] [IsLocalRing S], GlobalTheory.Mum.Base S → ∀ {H : Over (Sp S)} [GrpObj H]
      [IsCommMonObj H], IsSemiAbelian H → ∀ {E : DegData S (maximalIdeal S)} {B : PolAV (Sp (FractionRing S))}
      (W : Unif (maximalIdeal S) E B H) [Algebra (FractionRing S) F] (k : ℕ), 1 ≤ k → ∀ p : QkPt E.toPre F k,
      ∃ x : TFK (R := S) F ⟶ B.A, QkToAkU W.toUnifPre F k p x := by
    intro S _ _ _ hS H _ _ hH E B W _ k hk p
    obtain ⟨x, hx⟩ := GlobalTheory.TorsionAnyChar.existsTransl_any hL S (maximalIdeal S) hS.1 E B H hH W F k hk p
    exact ⟨x, (GlobalTheory.TorsionAnyChar.indAtTransl_any hL S (maximalIdeal S) hS.1 E B H hH W F k hk p x).1
      (hx 1 k le_rfl (mul_one k).symm p (one_smul _ _).symm rfl)⟩

  have key : ∀ k : ℕ, IsUnit (k : R) → ∀ τ' : Multiplicative D'.toPre.X →* Fˣ, τ' ^ k = 1 →
      ∀ χ, τ' (Multiplicative.ofAdd (ρ χ)) = τ' (Multiplicative.ofAdd (ρ' χ)) := by
    intro k hk τ' hτ' χ
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
    let τ₁ : Multiplicative D.toPre.X →* Fˣ := τ'.comp (AddMonoidHom.toMultiplicative ρ)
    let τ₂ : Multiplicative D.toPre.X →* Fˣ := τ'.comp (AddMonoidHom.toMultiplicative ρ')
    obtain ⟨q₁, y₁, t₁⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult (F := F) (k := k) τ₁
      (MonoidHom.ext fun χ => DFunLike.congr_fun hτ' _)
    obtain ⟨q₂, y₂, t₂⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult (F := F) (k := k) τ₂
      (MonoidHom.ext fun χ => DFunLike.congr_fun hτ' _)
    obtain ⟨q', y', t'⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D'.tau_bimult (F := F) (k := k) τ' hτ'
    obtain ⟨a₁, ha₁⟩ := img hR hG U k hk1 q₁
    obtain ⟨a₂, ha₂⟩ := img hR hG U k hk1 q₂
    obtain ⟨a', ha'⟩ := img hV hG' U' k hk1 q'
    have e₁ := h F hF k hk τ₁ τ' q₁ q' a₁ a' hτ' (fun _ => rfl) y₁ t₁ y' t' ha₁ ha'
    have e₂ := h' F hF k hk τ₂ τ' q₂ q' a₂ a' hτ' (fun _ => rfl) y₂ t₂ y' t' ha₂ ha'
    have e : a₁.left ≫ genMap U = a₂.left ≫ genMap U := e₁.trans e₂.symm

    have ea : a₁ = a₂ := by
      refine Over.OverMorphism.ext ?_
      have e' : a₁.left ≫ U.gen.inv.left = a₂.left ≫ U.gen.inv.left := by
        refine pullback.hom_ext ?_ ?_
        · simpa only [genMap, Category.assoc] using e
        · have w₁ := Over.w U.gen.inv
          have s : U.gen.inv.left ≫ pullback.snd G.hom (jK R) = A.A.hom := w₁
          rw [Category.assoc, Category.assoc, s, Over.w a₁, Over.w a₂]
      simpa using congrArg (· ≫ U.gen.hom.left) e'
    subst ea
    obtain ⟨z, hz, hh, hι, hadd⟩ := GlobalTheory.TorsionMapInj.qkToAk_injective_closed R (maximalIdeal R) hR.1 D A G hG U F k hk1
      q₁ q₂ a₁ ha₁ ha₂
    have hz0 : z = 0 := by
      rw [y₁, y₂, zero_add, eq_comm, ← natCast_zsmul] at hz
      exact (smul_eq_zero.1 hz).resolve_left (by exact_mod_cast hk0)
    subst hz0
    rw [GlobalTheory.TorusExt.isIota_iff_eq D.tau_bimult, map_zero] at hι
    subst hι
    rw [GlobalTheory.TorusExt.isAdd_iff_eq, add_zero] at hadd
    rw [hadd] at t₂
    have u := ((GlobalTheory.TorsionAnyChar.gtOnto_any hL R (maximalIdeal R) hR.1 D F).2.2.2.1 q₁.g t₁.1).unique t₁ t₂
    exact congrArg Units.val (DFunLike.congr_fun u (Multiplicative.ofAdd χ)) |> Units.ext
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℕ, 2 ≤ l ∧ IsUnit (l : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by simpa using h⟩
    · exact ⟨2, le_rfl, by simpa using h.neg⟩
  refine AddMonoidHom.ext fun χ => ?_
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_dvd hl2 _ fun n => ?_
  have hk : IsUnit ((l ^ n : ℕ) : R) := by simpa using hl.pow n
  have hkF : ((l ^ n : ℕ) : F) ≠ 0 := by
    have := hk.map ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))
    rw [map_natCast] at this
    exact this.ne_zero
  haveI : NeZero ((l ^ n : ℕ) : F) := ⟨hkF⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F (l ^ n)
  have hn0 : l ^ n ≠ 0 := pow_ne_zero _ (by omega)
  obtain ⟨z, hz⟩ := exists_eq_add_nsmul (ζ := (hζ.isUnit hn0).unit) (IsPrimitiveRoot.coe_units_iff.1 hζ)
    (key (l ^ n) hk · · χ)
  exact ⟨-z, by rw [hz, smul_neg]; abel⟩

end GlobalTheory.Poinc.Eq8
