import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenDecompBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentCoordsBaseChangeSmoothCommGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTLieSpread

theorem prod_ofFn_eq {G : Type} [Monoid G] {V : Type} [AddCommMonoid V] (T : V → G)
    (h0 : T 0 = 1) (hadd : ∀ c c', T (c + c') = T c * T c') :
    ∀ {a : ℕ} (w : Fin a → V), (List.ofFn (fun i => T (w i))).prod = T (∑ i, w i)
  | 0, w => by simp [h0]
  | a + 1, w => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ, hadd, prod_ofFn_eq T h0 hadd (fun i => w i.succ)]

theorem mat_ext {n : ℕ} {C : Type} [CommRing C] {A B : Matrix (Fin n) (Fin n) C}
    (h : ∀ v, A.mulVec v = B.mulVec v) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)

theorem isUnit_two_rho_sub {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) : IsUnit (2 * b.ρ - (D.tr : R)) := by
  have hsq : (2 * b.ρ - (D.tr : R)) ^ 2 = ((D.tr ^ 2 - 4 * D.nm : ℤ) : R) := by
    have := b.ρ_root; push_cast; linear_combination 4 * this
  have hd : D.tr ^ 2 - 4 * D.nm = -(((D.tr ^ 2 - 4 * D.nm).natAbs : ℕ) : ℤ) := by
    have := D.disc_neg; omega
  have hcop : ((D.tr ^ 2 - 4 * D.nm).natAbs).Coprime p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out)]
    intro h; exact D.disc_p (Int.natCast_dvd.mpr h)
  have hu := b.unit _ hcop
  rw [← isUnit_pow_iff (n := 2) two_ne_zero, hsq, hd]
  rw [Int.cast_neg, Int.cast_natCast]
  exact hu.neg

def TangentCoordinatesSmoothCommGroupLocalRing : Prop :=
  ∀ (W : Type) [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∃ (n : ℕ) (M : (G ⟶ G) → Matrix (Fin n) (Fin n) W), ∀ (R' : Type) [CommRing R'] (β : W →+* R'),
      ∃ T : (Fin n → R') → (GlobalTheory.UPel.HT.epsPtR (spMap β) ⟶ G), Function.Injective T ∧
        (∀ v : GlobalTheory.UPel.HT.epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left =
          (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) ∧
        (∀ c c', T (c + c') = T c * T c') ∧
        (∀ (s : R') c, (T (s • c)).left = spMap (epsScaleR s) ≫ (T c).left) ∧
        ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map β).mulVec c)

theorem spread_of_coord (hcoord : TangentCoordinatesSmoothCommGroupLocalRing) : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] (tR : R →+* C) (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A], Smooth A.hom → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), GlobalTheory.UPel.HT.LieAt b act tR (spMap (RingHom.id C)) → ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp C), x ≫ spMap tR = spMap β → GlobalTheory.UPel.HT.LieAt b act β x := by
  intro p _ D R _ b C _ _ tR A _ _ hsm act hlie R' _ β x hx
  obtain ⟨g0, rfl⟩ : ∃ g0 : C →+* R', spMap g0 = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  have hg : g0.comp tR = β := by
    have h1 : Spec.map (CommRingCat.ofHom (g0.comp tR)) = Spec.map (CommRingCat.ofHom β) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp]; exact hx
    have h2 := Spec.map_injective h1
    simpa using congrArg CommRingCat.Hom.hom h2
  have hgapp : ∀ r, g0 (tR r) = β r := fun r => by rw [← hg]; rfl
  obtain ⟨n, M, hM⟩ := hcoord C A hsm
  obtain ⟨T1, T1inj, T1rng, T1add, T1sm, T1u⟩ := hM C (RingHom.id C)
  obtain ⟨T0, T0inj, T0rng, T0add, T0sm, T0u⟩ := hM R' g0
  have T1zero : T1 0 = 1 := by
    have h := T1add 0 0; rw [add_zero] at h; exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have T0zero : T0 0 = 1 := by
    have h := T0add 0 0; rw [add_zero] at h; exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have hid : ∀ u : A ⟶ A, (M u).map (RingHom.id C) = M u := fun u => by ext; simp
  let fa : 𝓞 D.F → Matrix (Fin n) (Fin n) C := fun c => M (act.act (algebraMap (𝓞 D.F) D.O c))
  have key : ∀ (c : 𝓞 D.F) v, T1 v ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T1 ((fa c).mulVec v) := fun c v => by
    rw [T1u _ (act.hom _) v, hid]
  have f1 : fa 1 = 1 := mat_ext fun v => T1inj (by
    rw [← key, map_one, act.one, Category.comp_id, Matrix.one_mulVec])
  have fmul : ∀ c d, fa (c * d) = fa c * fa d := fun c d => mat_ext fun v => T1inj (by
    rw [← key, map_mul, act.mul, ← Category.assoc, key, key, Matrix.mulVec_mulVec])
  have fadd : ∀ c d, fa (c + d) = fa c + fa d := fun c d => mat_ext fun v => T1inj (by
    rw [← key, map_add, act.add, MonObj.comp_mul, key, key, ← T1add, Matrix.add_mulVec])
  have f0 : fa 0 = 0 := by
    have h := fadd 0 0; rw [add_zero] at h; exact add_left_cancel (h.symm.trans (add_zero _).symm)
  let f : 𝓞 D.F →+* Matrix (Fin n) (Fin n) C :=
    { toFun := fa, map_one' := f1, map_mul' := fmul, map_zero' := f0, map_add' := fadd }
  have keyf : ∀ (c : 𝓞 D.F) v, T1 v ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T1 ((f c).mulVec v) := key
  have keyg : ∀ (c : 𝓞 D.F) u, T0 u ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T0 (((f c).map g0).mulVec u) :=
    fun c u => T0u _ (act.hom _) u
  have hω : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hρ : (tR b.ρ) ^ 2 - (D.tr : C) * tR b.ρ + (D.nm : C) = 0 := by
    have := congrArg tR b.ρ_root; simpa using this
  have hunit : IsUnit (2 * tR b.ρ - (D.tr : C)) := by
    simpa [map_ofNat] using (isUnit_two_rho_sub b).map tR
  let t : Fin D.a → (𝓞 D.F →+* C) := fun i => tR.comp (b.t i)
  have ht : ∀ i, t i D.ω = tR b.ρ := fun i => by simp [t, b.t_ω]
  have hyp : ∀ v : Fin n → C, (f D.ω).mulVec v = tR b.ρ • v → ∃ w : Fin D.a → Fin n → C,
      (∀ i (c : 𝓞 D.F), (f c).mulVec (w i) = t i c • w i) ∧ v = ∑ i, w i := by
    intro v hv
    obtain ⟨w, hw, hvw⟩ := hlie (T1 v) ⟨(T1rng _).2 ⟨v, rfl⟩, by rw [keyf, hv]; exact T1sm _ _⟩
    choose w' hw' using fun i => (T1rng (w i)).1 (hw i 0).1
    refine ⟨w', fun i c => T1inj ?_, T1inj ?_⟩
    · rw [← keyf, hw' i]
      apply Over.OverMorphism.ext
      rw [T1sm, hw' i]
      exact (hw i c).2
    · rw [hvw, ← prod_ofFn_eq T1 T1zero T1add]
      simp only [hw']
  have L := GlobalTheory.eigen_decomp_base_change (𝓞 D.F) C n D.a D.ω D.tr D.nm hω f (tR b.ρ) hρ hunit t ht hyp R' g0
  intro v hv
  obtain ⟨v', rfl⟩ := (T0rng v).1 hv.1
  obtain ⟨w, hw, hvw⟩ := L v' (T0inj (by
    apply Over.OverMorphism.ext
    rw [← keyg, T0sm, hgapp]
    exact hv.2))
  refine ⟨fun i => T0 (w i), fun i c => ⟨(T0rng _).2 ⟨_, rfl⟩, ?_⟩, ?_⟩
  · rw [keyg, hw i c, T0sm]
    rw [show g0 (t i c) = β (b.t i c) from hgapp _]
  · rw [hvw, prod_ofFn_eq T0 T0zero T0add]

theorem lieAt_spread : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] (tR : R →+* C) (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A], Smooth A.hom → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), GlobalTheory.UPel.HT.LieAt b act tR (spMap (RingHom.id C)) → ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp C), x ≫ spMap tR = spMap β → GlobalTheory.UPel.HT.LieAt b act β x :=
  spread_of_coord GlobalTheory.T.exists_tangent_coords_base_change_smooth_comm_group

end GlobalTheory.HTLieSpread
