import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WpQTrivRight
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesTorsionPairingSeparationIntegra
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.SympQ
open GlobalTheory.Ex

theorem qq_free_of_torsion {C : Type} [Field C] [IsAlgClosed C] (N : NumD C) {k : ℕ} (hk : (k : C) ≠ 0) (a : ℕ)
    (hdiv : ∀ x : N.A, ∃ y, y ^ k = x)
    (e : (powMonoidHom k : N.A →* N.A).ker ≃* Multiplicative (Fin a → ZMod k)) :
    Nonempty (Qq N k ≃* Multiplicative (Fin (Module.finrank ℤ N.X + (a + Module.finrank ℤ N.X)) → ZMod k)) := by
  haveI : NeZero k := ⟨by rintro rfl; simp at hk⟩
  have hk0 : k ≠ 0 := NeZero.ne k
  obtain ⟨f⟩ := QStr.ker_struct N hk a e
  let v := Module.finBasis ℤ N.X
  let i₀ : (powMonoidHom k : N.Gt →* N.Gt).ker →* N.QT k := MonoidHom.mk'
    (fun g => ⟨(1, g.1), (show g.1 ^ k = 1 from g.2).trans N.io_zero.symm⟩)
    fun g g' => Subtype.ext (Prod.ext (_root_.mul_one _).symm rfl)
  let π₀ : N.QT k →* Multiplicative (Fin (Module.finrank ℤ N.X) → ZMod k) := MonoidHom.mk'
    (fun p => Multiplicative.ofAdd fun i => (v.repr p.1.1.toAdd i : ZMod k)) fun p q => by
      refine Multiplicative.toAdd.injective (funext fun i => ?_)
      simp
  have hπ₀ : ∀ p, π₀ p = 1 ↔ ∃ z : N.X, p.1.1.toAdd = k • z := fun p => by
    constructor
    · intro h
      have hd : ∀ i, (k : ℤ) ∣ v.repr p.1.1.toAdd i := fun i =>
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (congrFun (congrArg Multiplicative.toAdd h) i)
      choose c hc using hd
      refine ⟨∑ i, c i • v i, ?_⟩
      conv_lhs => rw [← v.sum_repr p.1.1.toAdd]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc, mul_smul, natCast_zsmul]
    · rintro ⟨z, hz⟩
      refine Multiplicative.toAdd.injective (funext fun i => ?_)
      change ((v.repr p.1.1.toAdd i : ℤ) : ZMod k) = 0
      rw [hz]
      simp
  let π : Qq N k →* Multiplicative (Fin (Module.finrank ℤ N.X) → ZMod k) :=
    QuotientGroup.lift _ π₀ (by
      rintro _ ⟨z, rfl⟩
      exact (hπ₀ _).2 ⟨z.toAdd, rfl⟩)
  refine QStr.split_ext k _ _ ?_ (((QuotientGroup.mk' _).comp i₀).comp f.symm.toMonoidHom) π ?_ ?_ ?_
  · intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨p.1.1, Subtype.ext (Prod.ext rfl (N.mem_QT.1 p.2).symm)⟩
  · refine Function.Injective.comp (g := (QuotientGroup.mk' _).comp i₀) ?_ f.symm.injective
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨z, hz⟩ := (QuotientGroup.eq_one_iff _).1 hg
    have h1 : k • z.toAdd = 0 := congrArg (fun q : N.QT k => q.1.1.toAdd) hz
    have h2 : N.io z.toAdd = g.1 := congrArg (fun q : N.QT k => q.1.2) hz
    have h3 : z.toAdd = 0 := (smul_eq_zero.1 ((natCast_zsmul _ _).trans h1)).resolve_left (Nat.cast_ne_zero.2 hk0)
    exact Subtype.ext (by rw [← h2, h3, N.io_zero]; rfl)
  · intro c
    let y : N.X := ∑ i, ((c.toAdd i).val : ℤ) • v i
    obtain ⟨b, hb⟩ := hdiv (N.io y).b
    obtain ⟨u, -, hu⟩ := QStr.root_over N hk0 (N.io y) b hb
    refine ⟨QuotientGroup.mk ⟨(Multiplicative.ofAdd y, u), hu⟩, Multiplicative.toAdd.injective (funext fun i => ?_)⟩
    change ((v.repr y i : ℤ) : ZMod k) = c.toAdd i
    have : v.repr y i = ((c.toAdd i).val : ℤ) := congrFun (v.repr_sum_self _) i
    rw [this]
    simp
  · intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    constructor
    · intro h
      obtain ⟨z, hz⟩ := (hπ₀ p).1 h
      have hg : (p.1.2 * (N.io z)⁻¹) ^ k = 1 := by
        rw [mul_pow, inv_pow, N.mem_QT.1 p.2, hz, N.io_nsmul, mul_inv_cancel]
      refine ⟨f ⟨_, hg⟩, ?_⟩
      change QuotientGroup.mk (i₀ (f.symm (f ⟨_, hg⟩))) = _
      rw [f.symm_apply_apply, ← qEq_iff_mk_eq]
      exact ⟨z, hz.trans (zero_add _).symm, (inv_mul_cancel_right _ _).symm⟩
    · rintro ⟨y, hy⟩
      rw [← hy]
      exact (hπ₀ (i₀ (f.symm y))).2 ⟨0, (smul_zero _).symm⟩

theorem qq_free : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n : ℕ), 0 < n → Nonempty (Additive (GlobalTheory.SympQ.Qq N n) ≃+ (Fin (2 * (D.toPre.P.g + Module.finrank ℤ D.toPre.X)) → ZMod n)) := by
  intro R _ _ _ hR D F _ _ _ N ν n hn
  have hL : Laws := GlobalTheory.allSixLaws.1
  haveI : IsNoetherianRing R := hR.1.1
  haveI : CharZero R := hR.2
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  have hk : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have tor : ∀ (b : N.A) (k : ℕ), ν.eA b ^ k = 1 ↔ b ^ k = 1 := fun b k => by
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have hdiv : ∀ x : N.A, ∃ y, y ^ n = x := fun x => by
    obtain ⟨y, hy⟩ := ValuesTorsion.exists_pow_eq hL D.toPre.P (jFK (R := R) F ≫ jK R) (ν.eA x) hn
    exact ⟨ν.eA.symm y, by rw [← map_pow, hy, MulEquiv.symm_apply_apply]⟩
  obtain ⟨e⟩ : Nonempty ((powMonoidHom n : N.A →* N.A).ker ≃* Multiplicative (Fin (2 * D.toPre.P.g) → ZMod n)) := by
    obtain ⟨v, hv, h⟩ := ValuesTorsion.exists_basis hL D.toPre.P (jFK (R := R) F ≫ jK R) hk
    refine ValuesTorsion.nonempty_equiv_of_basis hn.ne' (fun i => ν.eA.symm (v i))
      (fun i => by rw [← map_pow, hv, map_one]) fun y hy => ?_
    refine (existsUnique_congr fun c => ?_).1 (h (ν.eA y) ((tor _ _).2 hy))
    simp only [List.prod_ofFn, ← map_pow, ← map_prod, MulEquiv.symm_apply_eq]
  obtain ⟨f⟩ := qq_free_of_torsion N hk _ hdiv e
  have hr : Module.finrank ℤ N.X = Module.finrank ℤ D.toPre.X := ν.eX.toIntLinearEquiv.finrank_eq
  have h2 : Module.finrank ℤ N.X + (2 * D.toPre.P.g + Module.finrank ℤ N.X) =
      2 * (D.toPre.P.g + Module.finrank ℤ D.toPre.X) := by rw [hr]; ring
  rw [← h2]
  exact ⟨MulEquiv.toAdditiveLeft f⟩

end GlobalTheory.SympQ
end
