import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteOfIsClosedSplitTorusOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory

namespace TorusPiTorsion

open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
attribute [local instance] zuAlgebra

variable {k : Type} [Field k] {X : Type} [AddCommGroup X]

theorem val_splitTorusPoint (t : Multiplicative X →* kˣ) (b : X) :
    SplitTorus.val (splitTorusPoint t) b =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (t (Multiplicative.ofAdd b) : k) := by
  have h : (torusIso k X).hom.appTop.hom (chi X b) =
      (Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra k X))).inv.hom (AddMonoidAlgebra.single b 1) := by
    have := torusGamma_chi k X b
    rw [torusGamma, CommRingCat.comp_apply] at this
    rw [← this]
    simp
  rw [SplitTorus.val_eq, splitTorusPoint_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h,
    SplitTorus.specMap_appTop_apply]
  simp [torusEval_single]

theorem splitTorusPoint_comp_torusMap (t : Multiplicative X →* kˣ) (φ : X →+ X) :
    splitTorusPoint t ≫ SplitTorus.torusMap (Sp k) φ =
      splitTorusPoint (t.comp (AddMonoidHom.toMultiplicative φ)) :=
  SplitTorus.hom_ext fun b => by
    rw [SplitTorus.val_comp_torusMap, val_splitTorusPoint, val_splitTorusPoint]
    rfl

end TorusPiTorsion
end GlobalTheory

namespace GlobalTheory
namespace TorusPiTorsion

theorem finite_of_isClosed_torusZariski_of_smul {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite ℤ X]
    (hdiv : ∀ r : O, r ≠ 0 → ∃ m : ℤ, m ≠ 0 ∧ r ∣ (m : O)) {π : O} (hπ0 : π ≠ 0)
    (hπ : ¬ IsUnit π) {H : Subgroup (Multiplicative X →* kˣ)}
    (hH : IsClosed[torusZariski k X] (H : Set (Multiplicative X →* kˣ)))
    (hstab : ∀ (a : O), ∀ s ∈ H,
      s.comp (AddMonoidHom.toMultiplicative (DistribMulAction.toAddMonoidHom X a)) ∈ H)
    (htors : ∀ s ∈ H,
      s.comp (AddMonoidHom.toMultiplicative (DistribMulAction.toAddMonoidHom X π)) = 1 → s = 1) :
    Finite H := by
  let K : Submodule O X :=
    { carrier := {x | ∀ s ∈ H, s (Multiplicative.ofAdd x) = 1}
      add_mem' := fun {a b} ha hb s hs => by rw [ofAdd_add, map_mul, ha s hs, hb s hs, _root_.mul_one]
      zero_mem' := fun s _ => map_one s
      smul_mem' := fun a x hx s hs => hx _ (hstab a s hs) }
  have hK : ∀ x, x ∈ K ↔ ∀ s ∈ H, s (Multiplicative.ofAdd x) = 1 := fun x => Iff.rfl
  let N : Submodule O X := K ⊔ Ideal.span {π} • ⊤
  have hπN : ∀ x : X, π • x ∈ N := fun x =>
    Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial)
  haveI : Module.Finite O X := Module.Finite.of_restrictScalars_finite ℤ O X
  have hN : (⊤ : Submodule O X) ≤ N := by
    intro x _
    by_contra hx
    obtain ⟨m, hm0, c, hc⟩ := hdiv π hπ0
    have hmQ : ∀ q : X ⧸ N, m • q = 0 := fun q => by
      obtain ⟨y, rfl⟩ := N.mkQ_surjective q
      rw [← Int.cast_smul_eq_zsmul O, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        hc, mul_smul]
      exact hπN _
    have hmQ' : ∀ q : Multiplicative (X ⧸ N), q ^ m.natAbs = 1 := fun q => by
      have h1 : (m.natAbs : ℤ) • q.toAdd = 0 := by
        rcases Int.natAbs_eq m with h | h
        · rw [← h]; exact hmQ _
        · rw [show (m.natAbs : ℤ) = -m by omega, neg_smul, hmQ, neg_zero]
      rw [natCast_zsmul] at h1
      exact congrArg Multiplicative.ofAdd h1
    haveI : Module.Finite ℤ (X ⧸ N) :=
      Module.Finite.of_surjective N.mkQ.toAddMonoidHom.toIntLinearMap N.mkQ_surjective
    haveI : Finite (X ⧸ N) := Module.finite_of_fg_torsion _ fun q =>
      ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm0⟩, hmQ q⟩
    have hexp : Monoid.exponent (Multiplicative (X ⧸ N)) ≠ 0 := Monoid.exponent_ne_zero_of_finite
    haveI : NeZero ((Monoid.exponent (Multiplicative (X ⧸ N)) : ℕ) : k) := ⟨Nat.cast_ne_zero.2 hexp⟩
    obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
      (Multiplicative (X ⧸ N)) k (a := Multiplicative.ofAdd (N.mkQ x))
      (by simpa using hx)
    let t : Multiplicative X →* kˣ := φ.comp (AddMonoidHom.toMultiplicative N.mkQ.toAddMonoidHom)
    have ht : ∀ y, t y = φ (Multiplicative.ofAdd (N.mkQ y.toAdd)) := fun y => rfl
    have htH : t ∈ H := mem_of_isClosed_torusZariski hH fun y hy => by
      have : N.mkQ y.toAdd = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.mem_sup_left ((hK _).2 hy)
      rw [ht, this, ofAdd_zero, map_one]
    have ht1 : t = 1 := htors t htH (MonoidHom.ext fun y => by
      have : N.mkQ (π • y.toAdd) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hπN _
      change t (Multiplicative.ofAdd (π • y.toAdd)) = 1
      rw [ht, toAdd_ofAdd, this, ofAdd_zero, map_one])
    exact hφ (by simpa [ht] using DFunLike.congr_fun ht1 (Multiplicative.ofAdd x))
  obtain ⟨r, hr, hrK⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (I := Ideal.span {π}) (N := K) (N' := ⊤) (P := ⊤) Module.Finite.fg_top le_rfl hN
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hπ
    rw [zero_sub, Ideal.mem_span_singleton] at hr
    exact isUnit_of_dvd_one ((dvd_neg).1 hr)
  obtain ⟨m, hm0, c, hc⟩ := hdiv r hr0
  have hmK : ∀ x : X, m • x ∈ K := fun x => by
    rw [← Int.cast_smul_eq_zsmul O, hc, mul_smul]
    exact hrK (Submodule.smul_mem_pointwise_smul _ r ⊤ trivial)
  have hmH : ∀ s ∈ H, s ^ m.natAbs = 1 := fun s hs => by
    have h1 : s ^ m = 1 := MonoidHom.ext fun y => by
      have := (hK _).1 (hmK y.toAdd) s hs
      rw [ofAdd_zsmul, map_zpow, ofAdd_toAdd] at this
      rw [MonoidHom.zpow_apply, this, MonoidHom.one_apply]
    exact pow_natAbs_eq_one.2 h1
  exact (finite_setOf_pow_eq_one_torus (R := k) (X := X) (Int.natAbs_ne_zero.2 hm0)).subset
    (t := (H : Set (Multiplicative X →* kˣ))) fun s hs => hmH s hs

end TorusPiTorsion
end GlobalTheory

namespace GlobalTheory
namespace TorusPiTorsion

open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht

theorem exists_int_dvd (E : Type) [Field E] [NumberField E] (r : 𝓞 E) (hr : r ≠ 0) :
    ∃ m : ℤ, m ≠ 0 ∧ r ∣ (m : 𝓞 E) := by
  refine ⟨(Ideal.absNorm (Ideal.span {r}) : ℤ), ?_, ?_⟩
  · rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hr
  · rw [Int.cast_natCast, ← Ideal.mem_span_singleton]
    exact Ideal.absNorm_mem _

theorem finite_of_isClosed_of_no_pi_torsion :
    ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
      (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
      (act : OAct (𝓞 E) (splitTorus (Sp k) X)) (π : 𝓞 E), π ≠ 0 → ¬ IsUnit π →
      ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X))
        (Z : Set (splitTorus (Sp k) X).left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) →
        (∀ (a : 𝓞 E), ∀ x ∈ C, x ≫ act.act a ∈ C) → (∀ x ∈ C, x ≫ act.act π = 1 → x = 1) →
        Finite C := by
  intro E _ _ k _ _ _ X _ _ _ act π hπ0 hπ C Z hZ hC hstab htors
  have hφ : ∀ a, ∃ φ : X →+ X, act.act a = SplitTorus.torusMap (Sp k) φ := fun a => by
    haveI := act.hom a
    exact SplitTorus.exists_eq_torusMap _
  choose φ hφ using hφ
  have hinj : ∀ {ψ ψ' : X →+ X}, SplitTorus.torusMap (Sp k) ψ = SplitTorus.torusMap (Sp k) ψ' →
      ψ = ψ' := fun h => SplitTorus.torusMap_injective h
  have hone : φ 1 = AddMonoidHom.id X := hinj (by rw [← hφ, act.one, SplitTorus.torusMap_id])
  have hmul : ∀ a b, φ (a * b) = (φ a).comp (φ b) := fun a b =>
    hinj (by rw [← hφ, SplitTorus.torusMap_comp, ← hφ, ← hφ, act.mul])
  have hadd : ∀ a b, φ (a + b) = φ a + φ b := fun a b =>
    hinj (by rw [← hφ, SplitTorus.torusMap_add, ← hφ, ← hφ, act.add])
  let ρ : 𝓞 E →+* AddMonoid.End X :=
    { toFun := φ
      map_one' := hone
      map_mul' := hmul
      map_zero' := by
        have h := hadd 0 0
        rw [add_zero] at h
        have h' : φ 0 = 0 := by simpa using h.symm
        exact h'
      map_add' := hadd }
  letI : Module (𝓞 E) X := Module.compHom X ρ
  have hsmul : ∀ (a : 𝓞 E) (x : X), a • x = φ a x := fun a x => rfl
  let e := splitTorusPointEquiv k X
  have hpt : ∀ (s : Multiplicative X →* kˣ) (a : 𝓞 E), e s ≫ act.act a =
      e (s.comp (AddMonoidHom.toMultiplicative (DistribMulAction.toAddMonoidHom X a))) := by
    intro s a
    rw [hφ a]
    exact splitTorusPoint_comp_torusMap s (φ a)
  let H := C.comap e.toMonoidHom
  have hcl : IsClosed[torusZariski k X] (H : Set (Multiplicative X →* kˣ)) := by
    refine isClosed_induced_iff.2 ⟨(torusIso k X).hom ⁻¹' Z,
      hZ.preimage (torusIso k X).hom.continuous, ?_⟩
    ext t
    change _ ↔ splitTorusPoint t ∈ C
    rw [hC, range_splitTorusPoint_left, Set.singleton_subset_iff]
    rfl
  have h := finite_of_isClosed_torusZariski_of_smul (k := k) (O := 𝓞 E) (X := X)
    (exists_int_dvd E) hπ0 hπ hcl
    (fun a s hs => by
      change e _ ∈ C
      rw [← hpt]
      exact hstab a _ hs)
    (fun s hs h1 => e.injective (by
      rw [map_one]
      refine htors _ hs ?_
      change e s ≫ act.act π = 1
      rw [hpt, h1, map_one]))
  have e' : H ≃ C := e.toEquiv.subtypeEquiv fun _ => Iff.rfl
  exact e'.finite_iff.1 h

end TorusPiTorsion
end GlobalTheory
