import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfPowEqOne

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HtGen GlobalTheory.HalfGeo
open MonObj

namespace GlobalTheory.WeilHomGen

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_chars {G T K : Type} [CommGroup G] [CommGroup T] [Field K] {q : ℕ} (hq : q ≠ 0) (R : G → G → Kˣ → Prop)
    (hex : ∀ x y, x ^ q = 1 → y ^ q = 1 → ∃! c, R x y c)
    (hmul : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c'))
    (e : T →* G) (he : ∀ t, e t ^ q = 1) (hinj : Function.Injective e) (hsurj : ∀ g, g ^ q = 1 → ∃ t, e t = g)
    {N : ℕ} (s : Fin N → G) (ζ : Kˣ) (B : Matrix (Fin N) (Fin N) ℤ) (hζ : IsPrimitiveRoot ζ q) (hB : IsUnit B.det)
    (hs : ∀ m, s m ^ q = 1) (hG : ∀ m m', R (s m) (s m') (ζ ^ B m m'))
    (hgen : ∀ a : G, a ^ q = 1 → ∃ n : Fin N → ℕ, a = ∏ m, s m ^ n m) :
    ∃ χ : Fin N → (T →* Kˣ), (∀ m t, R (e t) (s m) (χ m t)) ∧
      ∀ χ' : T →* Kˣ, ∃ n : Fin N → ℕ, χ' = ∏ m, χ m ^ n m := by
  classical
  haveI : NeZero q := ⟨hq⟩
  choose f hf using fun m t => (hex (e t) (s m) (he t) (hs m)).exists
  have hfm : ∀ m t t', f m (t * t') = f m t * f m t' := fun m t t' =>
    (hex (e (t * t')) (s m) (he _) (hs m)).unique (hf m _) (by
      rw [map_mul]; exact hmul _ _ _ _ _ (hf m t) (hf m t'))
  let χ : Fin N → (T →* Kˣ) := fun m => MonoidHom.mk' (f m) (hfm m)
  refine ⟨χ, hf, fun χ' => ?_⟩
  choose σ hσ using fun m => hsurj (s m) (hs m)
  have hχσ : ∀ m k, χ m (σ k) = ζ ^ B k m := fun m k =>
    (hex (s k) (s m) (hs k) (hs m)).unique (hσ k ▸ hf m (σ k)) (hG k m)
  have hr : ∀ k, ∃ r : ℤ, ζ ^ r = χ' (σ k) := fun k => by
    have h1 : σ k ^ q = 1 := hinj (by rw [map_pow, he, map_one])
    have h2 : χ' (σ k) ∈ rootsOfUnity q K := by
      rw [mem_rootsOfUnity, ← map_pow, h1, map_one]
    rw [← hζ.zpowers_eq] at h2
    exact h2
  choose r hr using hr
  let v : Fin N → ℤ := B⁻¹.mulVec r
  have hv : B.mulVec v = r := by
    simp only [v, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hB, Matrix.one_mulVec]
  have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq
  refine ⟨fun m => (v m % q).toNat, ?_⟩
  have key : ∀ k, χ' (σ k) = (∏ m, χ m ^ (v m % q).toNat) (σ k) := fun k => by
    rw [← hr k, ← congrFun hv k, MonoidHom.finsetProd_apply]
    have s := map_prod (zpowersHom Kˣ ζ) (fun m => Multiplicative.ofAdd (B k m * v m)) Finset.univ
    rw [← ofAdd_sum] at s
    refine s.trans (Finset.prod_congr rfl fun m _ => ?_)
    have hz : (ζ ^ B k m) ^ q = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
    rw [MonoidHom.pow_apply, hχσ, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hq'),
      ← zpow_eq_zpow_emod' _ hz, ← zpow_mul]
    rfl
  refine MonoidHom.ext fun t => ?_
  obtain ⟨n, hn⟩ := hgen (e t) (he t)
  have ht : t = ∏ m, σ m ^ n m := hinj (by
    rw [hn, map_prod]
    exact Finset.prod_congr rfl fun m _ => by rw [map_pow, hσ])
  rw [ht, map_prod, map_prod]
  exact Finset.prod_congr rfl fun m _ => by rw [map_pow, map_pow, key]

theorem homSt : HomSt := by
  intro E _ _ _ H Dw l Xo c O _ β Z K _ ξ₀ ξ hξ q hq N s ζ B hζ hB hG hgen
  subst hξ
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.WeilTorsChar.exists_mulEquiv_points _ Z.t.G Z.oF.t.G Z.m.φ Z.m.cart (Over.mk ξ₀)
  let P := GlobalTheory.Obj.toPolAV Z.oF
  let e : TorsK Z.t (ξ₀ ≫ Z.j) q →* (Over.mk ξ₀ ⟶ Z.oF.t.G) :=
    Φ.symm.toMonoidHom.comp (TorsK Z.t (ξ₀ ≫ Z.j) q).subtype
  have he : ∀ t, e t = Φ.symm t.1 := fun _ => rfl
  obtain ⟨χ, h₁, h₂⟩ := exists_chars (K := K) hq
    (fun x y u => Out.WeilIs Z.oF.t.G Z.oF.t.PP.L (q : ℤ) x y (unitOn u))
    (fun x y hx hy => by
      obtain ⟨w, hw, hu⟩ := GlobalTheory.LevelCompare.weil_existsUnique P q x y hx hy
      obtain ⟨u, rfl⟩ := GlobalTheory.Ex.Specialise.unitOn_bijective.2 w
      exact ⟨u, hw, fun u' hu' => GlobalTheory.Ex.Specialise.unitOn_bijective.1 (hu _ hu')⟩)
    (fun x x' y u u' h h' => by
      have := weilIs_mul_left GlobalTheory.allSixLaws.1.globalFns _ P q _ x x' y _ _ h h'
      have e' : unitOn (u * u') = unitOn u * unitOn u' := map_mul (Units.map _) u u'
      rw [e']
      exact this)
    e (fun t => by
      have ht : t.1 ^ q = 1 := t.2
      rw [he]
      exact (map_pow Φ.symm _ _).symm.trans ((congrArg Φ.symm ht).trans (map_one _)))
    (Φ.symm.injective.comp Subtype.val_injective)
    (fun g hg => ⟨⟨Φ g, (map_pow Φ _ _).symm.trans ((congrArg Φ hg).trans (map_one _))⟩, Φ.symm_apply_apply g⟩)
    s ζ B hζ hB hG.1 hG.2 hgen
  refine ⟨χ, fun m k a ha => ?_, h₂⟩
  have : a = e k := by
    rw [he]
    refine (Φ.eq_symm_apply).2 (Over.OverMorphism.ext ?_)
    exact (hΦ a).trans ha
  rw [this]
  exact h₁ m k

end GlobalTheory.WeilHomGen
