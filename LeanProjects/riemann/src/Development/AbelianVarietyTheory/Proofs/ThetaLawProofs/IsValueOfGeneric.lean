import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsUnitThetaKeyRuleSmoothBase
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl GlobalTheory.KeyPow GlobalTheory.KeySmoothBase

noncomputable section
namespace GlobalTheory.KeySpec

theorem valueAt_of_point {κ : Rule} (hF : Funct κ) {S k : Type} [CommRing S] [Field k] [CharZero k] {y : KeyIn S} {u : S}
    (r : S →+* k) {xk : KeyIn k} (hk : KeyPB xk y r) (h : (κ k xk : k) = r u) : ValueAt κ y u (RingHom.ker r) := by
  intro K _ _ f x hf hx
  haveI := RingHom.ker_isPrime r
  haveI : CharZero (S ⧸ RingHom.ker r) := (RingHom.kerLift r).charZero
  obtain ⟨y', hy⟩ := exists_keyPB_ring y (Ideal.Quotient.mk (RingHom.ker r))
  let F := FractionRing (S ⧸ RingHom.ker r)
  obtain ⟨xF, hxF⟩ := exists_keyPB_ring y' (algebraMap _ F)
  have hr := RingHom.kerLift_injective r
  have er : (RingHom.kerLift r).comp (Ideal.Quotient.mk (RingHom.ker r)) = r :=
    RingHom.ext fun a => RingHom.kerLift_mk r a
  have e : (IsFractionRing.lift (K := F) hr).comp (algebraMap _ F) = RingHom.kerLift r :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap hr a
  have h1 := hF F k (IsFractionRing.lift hr) xF xk
    (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y' xF xk _ _ hxF
      (e.symm ▸ GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y y' xk _ _ hy (er.symm ▸ hk)))
  have h2 : (κ F xF : F) = algebraMap _ F (Ideal.Quotient.mk (RingHom.ker r) u) := by
    apply (IsFractionRing.lift (K := F) hr).injective
    rw [← h1, h, IsFractionRing.lift_algebraMap, RingHom.kerLift_mk]
  have hz : ∀ a ∈ RingHom.ker r, f a = 0 := fun a ha => (show a ∈ RingHom.ker f from hf ▸ ha)
  let g := Ideal.Quotient.lift (RingHom.ker r) f hz
  have eg : g.comp (Ideal.Quotient.mk _) = f := RingHom.ext fun a => Ideal.Quotient.lift_mk (RingHom.ker r) f hz
  have hg : RingHom.ker g = ⊥ := by
    refine le_antisymm (fun a ha => ?_) bot_le
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : a ∈ RingHom.ker f := ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hf ▸ this)
  exact valueAt_bot hF hxF h2 K g x hg (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y y' x _ _ hy (eg.symm ▸ hx))

theorem isValue_of_generic : ∀ κ : Rule, Funct κ → UnitSp κ → ∀ (S : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] [CharZero S] (y : KeyIn S) (u : S), (∀ (K : Type) [Field K] [CharZero K] (f : S →+* K) (x : KeyIn K), Function.Injective f → KeyPB x y f → (κ K x : K) = f u) → IsValue κ y u := by
  intro κ hF hU S _ _ _ _ y u h K _ _ f x hx
  have h0 : ValueAt κ y u ⊥ := fun K _ _ f x hf hx => h K f x ((RingHom.injective_iff_ker_eq_bot f).2 hf) hx
  by_cases hp : RingHom.ker f = ⊥
  · exact h0 K f x hp hx
  haveI := RingHom.ker_isPrime f
  obtain ⟨O, _, _, _, _, φ, hφ, hm⟩ :=
    GlobalTheory.exists_complete_discreteValuationRing_of_prime_lt (⊥ : Ideal S) (RingHom.ker f) (bot_lt_iff_ne_bot.2 hp)
  haveI : CharZero O := charZero_of_injective_ringHom ((RingHom.injective_iff_ker_eq_bot φ).2 hφ)
  obtain ⟨yO, hy⟩ := exists_keyPB_ring y φ
  obtain ⟨u', hu'⟩ := exists_unit_dvr hF hU O yO
  have e : φ u = u' := (h0.map_bot φ hφ hy).unique (hu' ⊥)
  have hk : RingHom.ker ((IsLocalRing.residue O).comp φ) = RingHom.ker f := by
    rw [← RingHom.comap_ker, IsLocalRing.ker_residue, hm]
  haveI : CharZero (IsLocalRing.ResidueField O) := charZero_of_inj_zero fun n hn => by
    have : (n : S) ∈ RingHom.ker ((IsLocalRing.residue O).comp φ) := by
      rw [RingHom.mem_ker, map_natCast, hn]
    rw [hk, RingHom.mem_ker, map_natCast] at this
    exact_mod_cast this
  obtain ⟨xk, hxk⟩ := exists_keyPB_ring yO (IsLocalRing.residue O)
  refine valueAt_of_point hF ((IsLocalRing.residue O).comp φ) (GlobalTheory.keyPB_trans _ _ _ y yO xk _ _ hy hxk) ?_ K f x hk.symm hx
  rw [hu' _ _ _ xk rfl hxk, RingHom.comp_apply, e]

end GlobalTheory.KeySpec
end
