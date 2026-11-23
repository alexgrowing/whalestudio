import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSubFiniteFree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke.FibreMulK

private theorem ev_nsmul' {p : ℕ} [Fact p.Prime] {D : Datum p} {k : Type} [Field k] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : TateIsoO D k Q act e) (n j : ℕ) (y : D.La) :
    I.ev n (j • y) = I.ev n y ^ j := by
  induction j with
  | zero =>
    have h := I.add n 0 0
    rw [add_zero] at h
    rw [zero_smul, _root_.pow_zero]
    exact mul_left_cancel (a := I.ev n 0) (by rw [_root_.mul_one]; exact h.symm)
  | succ j ih => rw [succ_nsmul, I.add, ih, _root_.pow_succ]

private theorem nsmul_cancel {M : Type} [AddCommGroup M] [Module.Free ℤ M] {k : ℕ} (hk : 0 < k) {x y : M}
    (h : k • x = k • y) : x = y := by
  have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  apply smul_right_injective M hk'
  simpa only [natCast_zsmul] using h

theorem fibre_mulK : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (k N : ℕ), 0 < k → 0 < N → k.Coprime p → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k * k) s) (K : Type) [Field K] [IsAlgClosed K] (y y' : Sp K ⟶ o.A.left), y ≫ ((𝟙 o.A) ^ k).left = y' ≫ ((𝟙 o.A) ^ k).left → ∃! a : GlobalTheory.UPel.HT.Hecke.heckeSub o LinearMap.id (N * k), y ≫ (GlobalTheory.UPel.HT.Hecke.transl a.1).left = y' := by
  intro p _ D R _ b k N hk hN hkp hNp S s o K _ _ y y' hyy
  set x : Sp K ⟶ S := y ≫ o.A.hom with hx
  have hx' : y' ≫ o.A.hom = x := by
    have e := congrArg (· ≫ o.A.hom) hyy
    simp only [Category.assoc, Over.w] at e
    exact e.symm
  let T : Over S := Over.mk x
  let yt : T ⟶ o.A := Over.homMk y rfl
  let yt' : T ⟶ o.A := Over.homMk y' hx'
  have hpow : yt ^ k = yt' ^ k := by
    have e : yt ≫ (𝟙 o.A) ^ k = yt' ≫ (𝟙 o.A) ^ k := Over.OverMorphism.ext hyy
    rwa [comp_pow, comp_pow, Category.comp_id, Category.comp_id] at e
  set d : T ⟶ o.A := yt⁻¹ * yt' with hd
  have hdk : d ^ k = 1 := by rw [hd, mul_pow, inv_pow, hpow, inv_mul_cancel]
  have hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := (Spec.map_preimage _).symm
  obtain ⟨I, hI⟩ := o.geom K x _ hβ
  have hcop : (N * k * k).Coprime p := Nat.Coprime.mul (Nat.Coprime.mul hNp hkp) hkp
  have hpos : 0 < N * k * k := Nat.mul_pos (Nat.mul_pos hN hk) hk
  obtain ⟨z, hz⟩ := (I.onto (N * k * k) hpos hcop d).1 (by
    rw [pow_mul, pow_right_comm, hdk, one_pow])
  have hkz : I.ev (N * k * k) (k • z) = 1 := by rw [ev_nsmul', hz, hdk]
  obtain ⟨w, hw⟩ := (I.ker (N * k * k) hpos hcop _).1 hkz
  haveI := D.freeLa
  have hzw : z = (N * k) • w := by
    apply nsmul_cancel hk
    rw [hw, smul_smul, show k * (N * k) = N * k * k by ring]
  have key : ∀ a : heckeSub o LinearMap.id (N * k), y ≫ (transl a.1).left = y' ↔ toUnit T ≫ a.1 = d := by
    intro a
    have e1 : yt ≫ transl a.1 = yt * (toUnit T ≫ a.1) := by
      rw [transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (yt ≫ toUnit o.A) (toUnit T)]
    constructor
    · intro h
      have e2 : yt ≫ transl a.1 = yt' := Over.OverMorphism.ext h
      rw [e1] at e2
      rw [hd, ← e2, inv_mul_cancel_left]
    · intro h
      have e2 : yt ≫ transl a.1 = yt' := by rw [e1, h, hd, mul_inv_cancel_left]
      exact congrArg CommaMorphism.left e2
  have hmem : o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w) ∈ heckeSub o LinearMap.id (N * k) :=
    mem_heckeSub o _ _ w
  refine ⟨⟨_, hmem⟩, (key _).2 ?_, ?_⟩
  · show toUnit T ≫ o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w) = d
    rw [LinearMap.id_apply, hI, ← hzw, hz]
  · intro a ha
    have h1 : toUnit T ≫ a.1 = d := (key a).1 ha
    have h2 : toUnit T ≫ o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w) = d := by
      rw [LinearMap.id_apply, hI, ← hzw, hz]
    have hm : a.1 * (o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w))⁻¹ ∈ heckeSub o LinearMap.id (N * k) :=
      Subgroup.mul_mem _ a.2 (Subgroup.inv_mem _ hmem)
    have h3 : toUnit T ≫ (a.1 * (o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w))⁻¹) = 1 := by
      have hi : toUnit T ≫ (o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w))⁻¹ = d⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← h2, ← comp_mul, inv_mul_cancel, comp_one]
      rw [comp_mul, h1, hi, mul_inv_cancel]
    have h4 := (heckeSub_finite_free p D R b LinearMap.id k (N * k) hk (Nat.mul_pos hN hk) hkp
      (Nat.Coprime.mul hNp hkp) S s o).2 K x _ hm h3
    exact Subtype.ext (mul_inv_eq_one.mp h4)

end GlobalTheory.UPel.HT.Hecke.FibreMulK
