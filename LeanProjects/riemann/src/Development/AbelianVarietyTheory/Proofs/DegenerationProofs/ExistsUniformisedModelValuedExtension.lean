import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullZetaEq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FullTorsionObjectExistsUniqueModuliPointStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.Ex.ExtModel

theorem exists_extend {F : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] (V : ValuationSubring F)
    {K : Type} [Field K] [CharZero K] (b : V →+* K) : ∃ bF : F →+* K, ∀ x : V, bF x = b x := by
  have hb : Function.Injective b := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have h1 : IsAlgebraic ℤ (x : F) := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic _)
    have h2 : IsAlgebraic ℤ x :=
      (isAlgebraic_algHom_iff (V.subtype.toIntAlgHom) Subtype.val_injective).1 h1
    refine Ideal.comap_ne_bot_of_algebraic_mem (I := RingHom.ker b) h0 hx h2 ?_
    refine (Submodule.eq_bot_iff _).2 fun n hn => ?_
    have h3 : b (algebraMap ℤ V n) = 0 := hn
    simpa using h3
  exact ⟨IsFractionRing.lift (K := F) hb, fun x => IsFractionRing.lift_algebraMap (K := F) hb x⟩

theorem mem_of_pow_mem {F : Type} [Field F] (V : ValuationSubring F) {x : F} {n : ℕ} (hn : 0 < n) (h : x ^ n ∈ V) :
    x ∈ V := by
  rw [← V.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff hn.ne').1 h

theorem exists_mdl_ext : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] (A : Lift a K) (o : Full D K), o.ρ = A.ρ → ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] [Algebra (FractionRing W) C], CDV W → CExt W (IsLocalRing.maximalIdeal W) C → ∀ (K₁ : Type) [Field K₁] [Algebra (FractionRing W) K₁] [Algebra.IsAlgebraic (FractionRing W) K₁] (gam : K₁ →+* C) (e : K →+* K₁) (φ : O' →+* W), (∀ x, gam (algebraMap (FractionRing W) K₁ x) = algebraMap (FractionRing W) C x) → (∀ x, e (algebraMap (FractionRing O') K (algebraMap O' _ x)) = algebraMap (FractionRing W) K₁ (algebraMap W _ (φ x))) → ∀ o' : Full D C, FullExt (gam.comp e) o o' → ∃ (M : Mdl o') (f : W →+* M.W), ∀ x, algebraMap (FractionRing M.W) C (algebraMap _ _ (f x)) = algebraMap (FractionRing W) C (algebraMap _ _ x) := by
  intro h1 h2 h3 h4 h5 h6 h7 E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a _ K _ _ _ A o hρ C _ _ _ _ _ W _ _ _ _ hW hC K₁ _ _ _
    gam e φ hg he o' hext
  have : CharZero K := o.charZero
  have := c.fin
  obtain ⟨bF, hbF⟩ := exists_extend (c.V W₀)
    (((algebraMap (FractionRing O') K).comp (algebraMap O' (FractionRing O'))).comp b)
  obtain ⟨ν, h₀, hν₁, hν₂⟩ := GlobalTheory.ReZeta.exists_exponent o.I.ζ A.I.ζ o.I.ζ_prim o.I.ζ_pow A.I.ζ_prim A.I.ζ_pow
  obtain ⟨g, rfl⟩ := GlobalTheory.ReZeta.exists_sim D ν hν₁ hν₂
  let o₁ : Full D K := withI o (GlobalTheory.LevelTwist.twist o.I g fun n m hn hm => ⟨hν₂ n m hn hm, hν₁ n hn⟩)
  let o₁' : Full D C := withI o' (GlobalTheory.LevelTwist.twist o'.I g fun n m hn hm => ⟨hν₂ n m hn hm, hν₁ n hn⟩)
  have hext₁ : FullExt (gam.comp e) o₁ o₁' := by
    obtain ⟨p₁, p₂, ψ, p₃, p₄, p₅, p₆⟩ := hext
    refine ⟨p₁, fun n hn => ?_, ψ, p₃, p₄, p₅, fun n v hn => p₆ n (g.f n v) hn⟩
    change ((o'.I.ζ n ^ g.ν n : Cˣ) : C) = gam.comp e ((o.I.ζ n ^ g.ν n : Kˣ) : K)
    rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, p₂ n hn]
  obtain ⟨q₁, -, q₃⟩ := GlobalTheory.T.fullTorsionObject_existsUnique_moduliPoint h1 h2 h3 h4 h5 h6 h7 E H D l Xo c W₀ Y K bF
  obtain ⟨y, ⟨hy, hyo⟩, -⟩ := q₁ o₁ (fun r hr => by
      have hm : r ∈ c.V W₀ := mem_of_pow_mem _ two_pos (by
        have : r ^ 2 = -(H.d : c.F) := Subtype.ext (by simpa [hr] using H.sqrt_neg_disc_sq)
        rw [this]; exact neg_mem (natCast_mem _ _))
      exact hρ.trans ((A.ρ_eq ⟨r, hm⟩ hr).trans (hbF ⟨r, hm⟩).symm))
    (fun z hz => by
      have hm : z ∈ c.V W₀ := mem_of_pow_mem _ l.A_pos (by
        have : z ^ l.A = 1 := Subtype.ext (by
          simpa [hz, zeta] using (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one)
        rw [this]; exact one_mem _)
      exact (congrArg Units.val (h₀ l.A l.A_pos)).trans ((A.ζ_eq ⟨z, hm⟩ hz).trans (hbF ⟨z, hm⟩).symm))
  have hF := q₃ C (gam.comp e) y o₁ o₁' hyo hext₁
  rw [spMap_comp', Category.assoc] at hF
  have hs : (spMap e ≫ y) ≫ Y.j ≫ Y.s = spMap (algebraMap (FractionRing W) K₁) ≫ jK W ≫ spMap (φ.comp b) := by
    rw [Model.j_s, Category.assoc, ← Category.assoc y, hy, ← spMap_comp', ← spMap_comp']
    change _ = spMap _ ≫ spMap (algebraMap W (FractionRing W)) ≫ _
    rw [← spMap_comp', ← spMap_comp']
    refine congrArg spMap (RingHom.ext fun x => ?_)
    exact (congrArg e (hbF x)).trans (he (b x))
  obtain ⟨M, f, -, -, -, hf, -⟩ := GlobalTheory.Ex.UnifModel.exists_mdl h1 h2 h3 h4 h5 h6 h7 E H D l Xo c W₀ Y C W hW hC K₁ gam hg
    (spMap e ≫ y) (φ.comp b) hs o₁' hF
  exact ⟨{ W := M.W, cdv := M.cdv, ext := M.ext, t := M.t, P := M.P, φ := M.φ, cart := M.cart, lb := M.lb, act := M.act },
    f, hf⟩

end GlobalTheory.Ex.ExtModel
