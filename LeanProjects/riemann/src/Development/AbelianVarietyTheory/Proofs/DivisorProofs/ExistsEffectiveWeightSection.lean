import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqOneOfGeometricPointsTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOneTrivialOnAxis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSiegelObjectPolarisationKernelKilled
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionOfBirigidifiedBundleTrivialOnSliceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

noncomputable section

namespace GlobalTheory.UPel.HT.GenKer

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R' : Type} [CommRing R'] [Algebra ℚ R'] {S : Scheme.{0}}

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (u : Sp B ⟶ Sp A) : ∃ β : A →+* B, u = spMap β :=
  ⟨(Spec.preimage u).hom, by simp [spMap]⟩

theorem charZero_of_hom {k : Type} [Field k] (β : R' →+* k) : CharZero k :=
  charZero_of_injective_ringHom (β.comp (algebraMap ℚ R')).injective

theorem pow_eq_one_geom {gb : GBase D.toG R'} {N : ℕ} {t : S ⟶ Sp R'} (o : GObj gb N t) (e : ℕ)
    (hEF : ∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S)
    (g : Over.mk x₀ ⟶ o.A) (M : ℕ) (hM : 0 < M) (hn : g ^ M = 1)
    (hg : ∃ u : (o.P.pull (lift (snd o.A (Over.mk x₀) ≫ g) (fst o.A (Over.mk x₀))).left).Gen, u.IsGen) :
    g ^ e = 1 := by
  obtain ⟨β, hβ⟩ := exists_spMap (x₀ ≫ t)
  haveI := charZero_of_hom β
  obtain ⟨I, -⟩ := o.geom k x₀ β hβ
  obtain ⟨y, hy⟩ : ∃ y : D.La, I.ev M y = g := (I.onto M hM g).1 hn
  have key : ∀ z : D.La, (M : ℤ) ∣ D.EF y z := by
    intro z
    have hm : 0 < M * 2 := by omega
    have ha : I.ev (M * 2) y ^ 2 = g := by rw [I.tower M 2 hM two_pos y, hy]
    have hc := GlobalTheory.WeilSqKer.weilIs_eq_one S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm o.ample k x₀ (M * 2)
      (Nat.cast_ne_zero.2 hm.ne') _ _ ((I.onto _ hm _).2 ⟨y, rfl⟩) ((I.onto _ hm _).2 ⟨z, rfl⟩) (ha ▸ hg) _
      (I.isom _ hm y z)
    have h1 : I.ζ (M * 2) ^ (2 * D.EF y z) = 1 :=
      GlobalTheory.Ex.Specialise.unitOn_bijective.1 (hc.trans (map_one _).symm)
    have h3 := ((I.ζ_prim (M * 2) hm).zpow_eq_one_iff_dvd _).1 h1
    have h4 : (M : ℤ) * 2 ∣ D.EF y z * 2 := by
      rw [mul_comm (D.EF y z)]; exact_mod_cast h3
    exact (mul_dvd_mul_iff_right (by norm_num : (2 : ℤ) ≠ 0)).1 h4
  let f : D.La →ₗ[ℤ] ℤ :=
    { toFun := fun z => D.EF y z / M
      map_add' := fun u v => by
        rw [map_add, Int.add_ediv_of_dvd_left (key u)]
      map_smul' := fun r u => by
        rw [map_smul, smul_eq_mul, smul_eq_mul, RingHom.id_apply, Int.mul_ediv_assoc _ (key u)] }
  have hf : ∀ z, (M : ℤ) * f z = D.EF y z := fun z => Int.mul_ediv_cancel' (key z)
  obtain ⟨w, hw⟩ := hEF f
  have hyw : e • y = M • w := by
    apply D.nondeg
    ext z
    have hwz : D.EF w z = e • f z := by rw [hw]; rfl
    simp only [map_nsmul, LinearMap.smul_apply, hwz, nsmul_eq_mul]
    rw [← hf z]; ring
  calc g ^ e = I.ev M y ^ e := by rw [hy]
    _ = I.ev M (e • y) := (KerBy.ev_nsmul (La := D.La) _ (I.add M) e y).symm
    _ = 1 := (I.ker M hM _).2 ⟨w, hyw⟩

theorem exists_coprime_pow_eq_one (p : ℕ) [Fact p.Prime] (D : Datum p) (R' : Type) [CommRing R'] [Algebra ℚ R']
    (gb : GBase D.toG R') (N : ℕ) (_hN : 3 ≤ N) (S : Scheme.{0}) (t : S ⟶ Sp R') (o : GObj gb N t) :
    ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ o.A),
      (∃ u : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, u.IsGen) → x ^ e = 1 := by
  obtain ⟨e, he, hEF⟩ := D.perfP
  refine ⟨e, he, fun T x hx => ?_⟩
  apply Over.OverMorphism.ext
  refine T.left.affineCover.hom_ext _ _ fun i => ?_
  obtain ⟨B, ⟨u⟩⟩ : ∃ B : CommRingCat.{0}, Nonempty (T.left.affineCover.X i ≅ Spec B) :=
    ⟨_, ⟨(T.left.affineCover.X i).isoSpec⟩⟩
  rw [← cancel_epi u.inv]
  let a : Sp B ⟶ T.left := u.inv ≫ T.left.affineCover.f i
  let a' : Over.mk (a ≫ T.hom) ⟶ T := Over.homMk a rfl
  have hx' := KerBy.gen_comp S o.A o.P T _ a' x hx
  obtain ⟨M, hM, hxM⟩ := GlobalTheory.T.isTorsion_of_birigidified_bundle_trivial_on_slice S o.A o.P o.ab o.isLB o.rig₁ o.rig₂ o.symm o.ample B (a ≫ T.hom) _ hx'
  have hu : IsUnit ((M : ℕ) : Γ(S, ⊤)) := by
    have h0 : IsUnit ((M : ℕ) : R') := by
      simpa using (IsUnit.mk0 (M : ℚ) (Nat.cast_ne_zero.2 hM.ne')).map (algebraMap ℚ R')
    simpa using (h0.map (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom).map t.appTop.hom
  have h := GlobalTheory.TorsGeomPow.pow_eq_one_of_geometric_points S o.A o.ab M hu _ _ hxM e fun k _ _ ξ =>
    pow_eq_one_geom o e hEF k _ _ M hM (by rw [← MonObj.comp_pow, hxM, MonObj.comp_one])
      (KerBy.gen_comp S o.A o.P _ _ _ _ hx')
  have h' : a' ≫ x ^ e = a' ≫ 1 := by rw [MonObj.comp_pow, h, MonObj.comp_one]
  have h'' : a ≫ (x ^ e).left = a ≫ (1 : T ⟶ o.A).left := congrArg (fun z => z.left) h'
  exact (Category.assoc _ _ _).symm.trans (h''.trans (Category.assoc _ _ _))

end GlobalTheory.UPel.HT.GenKer
