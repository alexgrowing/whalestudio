import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

noncomputable section

namespace ProjTwist

def fpow (f : A) (n : ℕ) : Submonoid.powers f := ⟨f ^ n, (Submonoid.mem_powers_iff _ _).2 ⟨n, rfl⟩⟩

@[simp] lemma coe_fpow (f : A) (n : ℕ) : (fpow f n : A) = f ^ n := rfl

lemma fpow_add (f : A) (n m : ℕ) : fpow f (n + m) = fpow f n * fpow f m :=
  Subtype.ext (pow_add f n m)

def locMap {f : A} (x : ProjectiveSpectrum 𝒜) (hx : f ∉ x.asHomogeneousIdeal) :
    Localization.Away f →+* Loc 𝒜 x :=
  IsLocalization.map (M := Submonoid.powers f) (T := x.asHomogeneousIdeal.toIdeal.primeCompl) _
    (RingHom.id _) (Submonoid.powers_le.mpr hx)

lemma locMap_mk {f : A} (x : ProjectiveSpectrum 𝒜) (hx : f ∉ x.asHomogeneousIdeal) (a : A)
    (n : ℕ) :
    locMap x hx (Localization.mk a (fpow f n)) =
      Localization.mk a ⟨f ^ n, (Submonoid.powers_le.mpr hx) ⟨n, rfl⟩⟩ := by
  rw [locMap, Localization.mk_eq_mk', IsLocalization.map_mk', Localization.mk_eq_mk']
  rfl

lemma locMap_algebraMap {f : A} (x : ProjectiveSpectrum 𝒜) (hx : f ∉ x.asHomogeneousIdeal)
    (a : A) : locMap x hx (algebraMap A _ a) = algebraMap A _ a := by
  rw [locMap, IsLocalization.map_eq]
  rfl

lemma locMap_comp {f f' : A} (φ : Localization.Away f →+* Localization.Away f')
    (hφ : φ.comp (algebraMap A _) = algebraMap A _) (x : ProjectiveSpectrum 𝒜)
    (hx : f' ∉ x.asHomogeneousIdeal) (hx' : f ∉ x.asHomogeneousIdeal) (z : Localization.Away f) :
    locMap x hx (φ z) = locMap x hx' z := by
  have : (locMap x hx).comp φ = locMap x hx' := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    simp only [RingHom.comp_apply]
    rw [← RingHom.comp_apply φ, hφ, locMap_algebraMap, locMap_algebraMap]
  exact congrArg (fun F => F z) this

variable (𝒜) in

def awayDeg {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) (k : ℤ) :
    AddSubgroup (Localization.Away f) where
  carrier := {z | ∃ (n j : ℕ) (a : A), a ∈ 𝒜 j ∧ (j : ℤ) = n * d + k ∧
    z = Localization.mk a (fpow f n)}
  zero_mem' := ⟨(-k).toNat, (-k).toNat * d + k.toNat - (-k).toNat, 0, zero_mem _, by
    have : (-k).toNat ≤ (-k).toNat * d := Nat.le_mul_of_pos_right _ hd
    omega, by rw [Localization.mk_zero]⟩
  add_mem' := by
    rintro _ _ ⟨n, j, a, ha, hj, rfl⟩ ⟨m, j', b, hb, hj', rfl⟩
    refine ⟨n + m, j + m * d, f ^ n * b + f ^ m * a, add_mem ?_ ?_, ?_, ?_⟩
    · have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded n hf) hb
      have e : n • d + j' = j + m * d := by
        have : ((n • d + j' : ℕ) : ℤ) = ((j + m * d : ℕ) : ℤ) := by
          push_cast [smul_eq_mul]; linarith
        exact_mod_cast this
      rwa [e] at h
    · have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded m hf) ha
      rwa [smul_eq_mul, add_comm] at h
    · push_cast; linarith
    · rw [Localization.add_mk, fpow_add]
      rfl
  neg_mem' := by
    rintro _ ⟨n, j, a, ha, hj, rfl⟩
    exact ⟨n, j, -a, neg_mem ha, hj, by rw [Localization.neg_mk]⟩

lemma mul_mem_awayDeg {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) {k₁ k₂ : ℤ}
    {z w : Localization.Away f} (hz : z ∈ awayDeg 𝒜 hf hd k₁) (hw : w ∈ awayDeg 𝒜 hf hd k₂) :
    z * w ∈ awayDeg 𝒜 hf hd (k₁ + k₂) := by
  obtain ⟨n, j, a, ha, hj, rfl⟩ := hz
  obtain ⟨m, j', b, hb, hj', rfl⟩ := hw
  refine ⟨n + m, j + j', a * b, SetLike.mul_mem_graded ha hb, by push_cast; linarith, ?_⟩
  rw [Localization.mk_mul, fpow_add]

lemma mk_mem_awayDeg {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) {k : ℤ} {n j : ℕ} {a : A}
    (ha : a ∈ 𝒜 j) (hj : (j : ℤ) = n * d + k) :
    Localization.mk a (fpow f n) ∈ awayDeg 𝒜 hf hd k :=
  ⟨n, j, a, ha, hj, rfl⟩

lemma exists_val_eq_of_mem_awayDeg_zero {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    {z : Localization.Away f} (hz : z ∈ awayDeg 𝒜 hf hd 0) :
    ∃ z₀ : HomogeneousLocalization.Away 𝒜 f, z₀.val = z := by
  obtain ⟨n, j, a, ha, hj, rfl⟩ := hz
  have e : n • d = j := by
    have : ((n • d : ℕ) : ℤ) = j := by push_cast [smul_eq_mul]; linarith
    exact_mod_cast this
  refine ⟨HomogeneousLocalization.mk ⟨j, ⟨a, ha⟩, ⟨f ^ n, e ▸ SetLike.pow_mem_graded n hf⟩,
    (fpow f n).2⟩, ?_⟩
  rw [HomogeneousLocalization.val_mk]
  rfl

lemma nmem_of_mem {f : A} (x : Proj.basicOpen 𝒜 f) : f ∉ x.1.asHomogeneousIdeal := x.2

def toSection {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) (k : ℤ) :
    awayDeg 𝒜 hf hd k →+ Γ(twistingSheaf 𝒜 k, Proj.basicOpen 𝒜 f) where
  toFun z := mkSection (fun x => locMap x.1 (nmem_of_mem x) z.1) (fun x => by
    obtain ⟨n, j, a, ha, hj, hz⟩ := z.2
    refine ⟨Proj.basicOpen 𝒜 f, x.2, 𝟙 _, n * d, j, by push_cast; linarith, a, f ^ n, ha,
      ?_, fun y h => nmem_of_mem y (y.1.isPrime.mem_of_pow_mem n h), fun y => ?_⟩
    · have := SetLike.pow_mem_graded n hf
      rwa [smul_eq_mul] at this
    · change locMap y.1 (nmem_of_mem y) z.1 = _
      rw [hz]
      exact locMap_mk y.1 (nmem_of_mem y) a n)
  map_zero' := by
    ext x
    exact map_zero _
  map_add' z w := by
    ext x
    exact map_add _ _ _

lemma val_mem_awayDeg_zero {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (z₀ : HomogeneousLocalization.Away 𝒜 f) : z₀.val ∈ awayDeg 𝒜 hf hd 0 := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf z₀
  rw [HomogeneousLocalization.Away.val_mk]
  exact mk_mem_awayDeg hf hd ha (by push_cast [smul_eq_mul]; ring)

lemma isLocallyFraction_mul {U : Opens (ProjectiveSpectrum.top 𝒜)} {k₁ k₂ k₃ : ℤ}
    (hk : k₁ + k₂ = k₃) {a b : ∀ x : U, Loc 𝒜 x.1} (ha : (isLocallyFraction 𝒜 k₁).pred a)
    (hb : (isLocallyFraction 𝒜 k₂).pred b) : (isLocallyFraction 𝒜 k₃).pred (a * b) := fun x => by
  obtain ⟨Va, ma, ia, i, j, hij, r, s, hr, hs, hsn, wa⟩ := ha x
  obtain ⟨Vb, mb, ib, i', j', hij', r', s', hr', hs', hsn', wb⟩ := hb x
  refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, i + i', j + j', by push_cast; omega,
    r * r', s * s', SetLike.mul_mem_graded hr hr', SetLike.mul_mem_graded hs hs',
    fun ⟨y, hya, hyb⟩ => nmem_mul (hsn ⟨y, hya⟩) (hsn' ⟨y, hyb⟩), fun ⟨y, hya, hyb⟩ => ?_⟩
  have e1 : a (ia ⟨y, hya⟩) = _ := wa ⟨y, hya⟩
  have e2 : b (ib ⟨y, hyb⟩) = _ := wb ⟨y, hyb⟩
  change a (ia ⟨y, hya⟩) * b (ib ⟨y, hyb⟩) = _
  rw [e1, e2, Localization.mk_mul]
  rfl

lemma isLocallyFraction_locMap {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) {k : ℤ}
    {z : Localization.Away f} (hz : z ∈ awayDeg 𝒜 hf hd k) :
    (isLocallyFraction 𝒜 k).pred
      (fun x : (Proj.basicOpen 𝒜 f : Opens (ProjectiveSpectrum.top 𝒜)) =>
        locMap x.1 (nmem_of_mem x) z) :=
  (toSection hf hd k ⟨z, hz⟩).2

set_option backward.isDefEq.respectTransparency.types false in
open ProjectiveSpectrum in

lemma exists_section_of_isLocallyFraction_zero {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (t : ∀ x : U, Loc 𝒜 x.1) (ht : (isLocallyFraction 𝒜 0).pred t) :
    ∃ t' : (Proj.structureSheaf 𝒜).obj.obj (op U), ∀ x, (t'.1 x).val = t x := by
  have key : ∀ x : U, ∃ (V : Opens (ProjectiveSpectrum.top 𝒜)) (_ : x.1 ∈ V) (iV : V ⟶ U)
      (j : ℕ) (r s : 𝒜 j) (s_nin : ∀ y : V, s.1 ∉ y.1.asHomogeneousIdeal),
      ∀ y : V, t (iV y : U) = Localization.mk r.1 ⟨s.1, s_nin y⟩ := by
    intro x
    obtain ⟨V, hxV, iV, i, j, hij, r, s, hr, hs, hsn, w⟩ := ht x
    have e : i = j := by omega
    subst e
    exact ⟨V, hxV, iV, i, ⟨r, hr⟩, ⟨s, hs⟩, hsn, w⟩
  have pt : ∀ x : U, ∃ y : HomogeneousLocalization.AtPrime 𝒜
      x.1.asHomogeneousIdeal.toIdeal, y.val = t x := by
    intro x
    obtain ⟨V, hxV, iV, j, r, s, hsn, w⟩ := key x
    exact ⟨HomogeneousLocalization.mk ⟨j, r, s,
      (show s.1 ∈ x.1.asHomogeneousIdeal.toIdeal.primeCompl from hsn ⟨x.1, hxV⟩)⟩,
      by rw [HomogeneousLocalization.val_mk]; exact (w ⟨x.1, hxV⟩).symm⟩
  choose g hg using pt
  refine ⟨(⟨g, fun x => ?_⟩ : (StructureSheaf.structureSheafInType 𝒜).obj.obj (op U)), hg⟩
  obtain ⟨V, hxV, iV, j, r, s, hsn, w⟩ := key x
  refine ⟨V, hxV, iV, j, r, s, hsn, fun y => HomogeneousLocalization.val_injective _ ?_⟩
  rw [HomogeneousLocalization.val_mk]
  exact (hg _).trans (w y)

theorem toSection_bijective {f u g : A} {e : ℕ} (hu : u ∈ 𝒜 1) (hg : g ∈ 𝒜 e)
    (hfug : f = u * g) (hf : f ∈ 𝒜 (e + 1)) (k : ℤ) :
    Function.Bijective (toSection hf (Nat.succ_pos e) k) := by
  set hd := Nat.succ_pos e
  have hk : (k.toNat : ℤ) - ((-k).toNat : ℤ) = k := by omega

  set c : Localization.Away f := Localization.mk (u ^ (-k).toNat * g ^ k.toNat) (fpow f k.toNat)
  set c' : Localization.Away f := Localization.mk (u ^ k.toNat * g ^ (-k).toNat) (fpow f (-k).toNat)
  have hc : c ∈ awayDeg 𝒜 hf hd (-k) := by
    refine mk_mem_awayDeg hf hd (j := (-k).toNat + k.toNat * e) ?_ ?_
    · have h1 := SetLike.pow_mem_graded (-k).toNat hu
      have h2 := SetLike.pow_mem_graded k.toNat hg
      have := SetLike.mul_mem_graded h1 h2
      simpa [smul_eq_mul, mul_comm] using this
    · push_cast; linarith
  have hc' : c' ∈ awayDeg 𝒜 hf hd k := by
    refine mk_mem_awayDeg hf hd (j := k.toNat + (-k).toNat * e) ?_ ?_
    · have h1 := SetLike.pow_mem_graded k.toNat hu
      have h2 := SetLike.pow_mem_graded (-k).toNat hg
      have := SetLike.mul_mem_graded h1 h2
      simpa [smul_eq_mul, mul_comm] using this
    · push_cast; linarith
  have hcc' : c * c' = 1 := by
    rw [Localization.mk_mul, ← fpow_add, ← Localization.mk_self (fpow f (k.toNat + (-k).toNat))]
    congr 1
    rw [coe_fpow, hfug]
    ring
  have hloc : ∀ x : Proj.basicOpen 𝒜 f,
      locMap x.1 (nmem_of_mem x) c * locMap x.1 (nmem_of_mem x) c' = 1 := fun x => by
    rw [← map_mul, hcc', map_one]
  have hiso := (Proj.basicOpenIsoAway 𝒜 f hf hd).commRingCatIsoToRingEquiv.bijective
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    have hz' : ∀ x : Proj.basicOpen 𝒜 f, locMap x.1 (nmem_of_mem x) z.1 = 0 := fun x =>
      congrFun (congrArg val hz) x
    have hw : c * z.1 ∈ awayDeg 𝒜 hf hd 0 := by
      have := mul_mem_awayDeg hf hd hc z.2
      rwa [neg_add_cancel] at this
    obtain ⟨z₀, hz₀⟩ := exists_val_eq_of_mem_awayDeg_zero hf hd hw
    have h0 : (Proj.awayToSection 𝒜 f).hom z₀ = 0 := by
      apply Subtype.ext
      funext x
      apply HomogeneousLocalization.val_injective
      have h := ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 f z₀ x
      have h' : locMap x.1 (nmem_of_mem x) z₀.val = 0 := by
        rw [hz₀, map_mul, hz' x, mul_zero]
      exact h.trans (h'.trans HomogeneousLocalization.val_zero.symm)
    have hz0 : z₀ = 0 := by
      apply hiso.1
      exact h0.trans (map_zero _).symm
    have hcz : c * z.1 = 0 := by rw [← hz₀, hz0, HomogeneousLocalization.val_zero]
    apply Subtype.ext
    change z.1 = 0
    calc z.1 = c' * (c * z.1) := by rw [← mul_assoc, mul_comm c', hcc', one_mul]
      _ = 0 := by rw [hcz, mul_zero]
  · intro s
    have ht := isLocallyFraction_mul (neg_add_cancel k) (isLocallyFraction_locMap hf hd hc)
      (isLocallyFraction_val s)
    obtain ⟨t', ht'⟩ := exists_section_of_isLocallyFraction_zero _ ht
    obtain ⟨z₀, hz₀⟩ := hiso.2 t'
    have hz₀' : (Proj.awayToSection 𝒜 f).hom z₀ = t' := hz₀
    have hmem : c' * z₀.val ∈ awayDeg 𝒜 hf hd k := by
      have := mul_mem_awayDeg hf hd hc' (val_mem_awayDeg_zero hf hd z₀)
      rwa [add_zero] at this
    refine ⟨⟨c' * z₀.val, hmem⟩, ?_⟩
    subst hz₀'
    ext x
    have e1 : locMap x.1 (nmem_of_mem x) z₀.val =
        (((Proj.awayToSection 𝒜 f).hom z₀).1 x).val :=
      (ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 f z₀ x).symm
    have e2 : (((Proj.awayToSection 𝒜 f).hom z₀).1 x).val =
        locMap x.1 (nmem_of_mem x) c * val s x := ht' x
    show locMap x.1 (nmem_of_mem x) (c' * z₀.val) = val s x
    rw [map_mul, e1, e2]
    linear_combination (val s x) * hloc x

end ProjTwist

end

end GroundTheory.Arith.SchemeCoh
