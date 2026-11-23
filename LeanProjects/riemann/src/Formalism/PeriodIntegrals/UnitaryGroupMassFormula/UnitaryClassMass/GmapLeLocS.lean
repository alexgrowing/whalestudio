import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LSBase

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory PI.UnitaryGroupMassFormula.UJClassFin

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Glob

variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V] {M : ℕ}

private theorem mem_locS_iff' (S : Submonoid (𝓞 E)) (X : Submodule (𝓞 E) V) (x : V) :
    x ∈ locS S X ↔ ∃ s ∈ S, s • x ∈ X := Iff.rfl

theorem locS_mono (S : Submonoid (𝓞 E)) {X Y : Submodule (𝓞 E) V} (h : X ≤ Y) : locS S X ≤ locS S Y := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := hx
  exact (mem_locS_iff' S Y x).2 ⟨s, hs, h hx⟩

theorem le_locS (S : Submonoid (𝓞 E)) (X : Submodule (𝓞 E) V) : X ≤ locS S X := fun x hx => (mem_locS_iff' S X x).2 ⟨1, S.one_mem, by simpa using hx⟩

theorem locS_locS (S : Submonoid (𝓞 E)) (X : Submodule (𝓞 E) V) : locS S (locS S X) = locS S X := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, t, ht, hx⟩ := hx
    exact (mem_locS_iff' S X x).2 ⟨t * s, S.mul_mem ht hs, by rwa [mul_smul]⟩
  · exact le_locS S _

theorem locS_eq_of (S : Submonoid (𝓞 E)) {X Y : Submodule (𝓞 E) V} (h1 : X ≤ locS S Y) (h2 : Y ≤ locS S X) :
    locS S X = locS S Y := le_antisymm ((locS_mono S h1).trans (locS_locS S Y).le) ((locS_mono S h2).trans (locS_locS S X).le)

theorem osmul_comm (u : V ≃ₗ[E] V) (s : 𝓞 E) (w : V) : u (s • w) = s • u w := by
  rw [← algebraMap_smul E s w, map_smul, algebraMap_smul]

theorem gmap_locS (u : V ≃ₗ[E] V) (S : Submonoid (𝓞 E)) (X : Submodule (𝓞 E) V) :
    gmap u (locS S X) = locS S (gmap u X) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    mem_locS_iff']
  constructor
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    exact ⟨s, hs, s • y, hy, osmul_comm u s y⟩
  · rintro ⟨s, hs, z, hz, hzx⟩
    refine ⟨u.symm x, ⟨s, hs, ?_⟩, by simp⟩
    have hsz : s • u.symm x = z := by
      apply u.injective
      rw [osmul_comm, LinearEquiv.apply_symm_apply, hzx]
    rw [hsz]
    exact hz

theorem gmap_comp (u w : V ≃ₗ[E] V) (X : Submodule (𝓞 E) V) : gmap (u * w) X = gmap u (gmap w X) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨w y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩

theorem gmap_le_locS (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (S : Submonoid (𝓞 E))
    (K : GL (Fin M) E)
    (h : ∀ x ∈ crdOf b L0, ∃ s ∈ S, (algebraMap (𝓞 E) E s) • (K : Matrix (Fin M) (Fin M) E).mulVec x ∈ crdOf b L0) :
    gmap (linOf b K) L0 ≤ locS S L0 := by
  intro y hy
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hy
  obtain ⟨v, hv, rfl⟩ := hy
  have hx : (b.repr v : Fin M → E) ∈ crdOf b L0 := by
    show ∑ i, b.repr v i • b i ∈ L0
    rw [b.sum_repr]
    exact hv
  obtain ⟨s, hs, hK⟩ := h _ hx
  refine (mem_locS_iff' S L0 _).2 ⟨s, hs, ?_⟩
  have e : linOf b K v = ∑ j, ((K : Matrix (Fin M) (Fin M) E).mulVec (b.repr v)) j • b j := by
    simp only [linOf, LinearEquiv.ofLinear_apply, Matrix.toLin_apply]
  have hK' : ∑ i, ((algebraMap (𝓞 E) E s) • ((K : Matrix (Fin M) (Fin M) E).mulVec (b.repr v))) i • b i ∈ L0 := hK
  rw [e, ← algebraMap_smul E s, Finset.smul_sum]
  convert hK' using 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_smul]

private theorem sum_mem_crdOf (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {ι : Type}
    (t : Finset ι) (z : ι → Fin M → E) (hz : ∀ i ∈ t, z i ∈ crdOf b L0) :
    ∑ i ∈ t, z i ∈ crdOf b L0 := by
  show ∑ j, (∑ i ∈ t, z i) j • b j ∈ L0
  simp only [Finset.sum_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact L0.sum_mem fun i hi => hz i hi

private theorem algebraMap_smul_mem_crdOf (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (s : 𝓞 E)
    {x : Fin M → E} (hx : x ∈ crdOf b L0) : (algebraMap (𝓞 E) E s) • x ∈ crdOf b L0 := by
  show ∑ j, ((algebraMap (𝓞 E) E s) • x) j • b j ∈ L0
  have h := L0.smul_mem s (show ∑ j, x j • b j ∈ L0 from hx)
  rw [Finset.smul_sum] at h
  convert h using 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_smul, algebraMap_smul]

private theorem add_mem_crdOf (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V)
    {x y : Fin M → E} (hx : x ∈ crdOf b L0) (hy : y ∈ crdOf b L0) : x + y ∈ crdOf b L0 := by
  show ∑ j, (x + y) j • b j ∈ L0
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  exact L0.add_mem hx hy

theorem glob_stab {F : Type} [Field F] [Algebra F E] (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V)
    {u k : ℕ} (hu : ∀ x ∈ crdOf b L0, ∀ i, IsIntegral ℤ ((u : F) • x i))
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ crdOf b L0)
    (Y : Matrix (Fin M) (Fin M) E) (s : 𝓞 E) (e : Fin M → Fin M → E) (he : ∀ i j, IsIntegral ℤ (e i j))
    (hY : ∀ i j, (algebraMap (𝓞 E) E s) * (Y - 1) i j = ((u * k : ℕ) : E) * e i j)
    {x : Fin M → E} (hx : x ∈ crdOf b L0) : (algebraMap (𝓞 E) E s) • Y.mulVec x ∈ crdOf b L0 := by
  have key : ∀ i0, (algebraMap (𝓞 E) E s) * (Y.mulVec x) i0 =
      (algebraMap (𝓞 E) E s) * x i0 + ∑ j, ((k : F) • (e i0 j * ((u : F) • x j))) := by
    intro i0
    have hsplit : ∀ j, (algebraMap (𝓞 E) E s) * Y i0 j =
        ((u * k : ℕ) : E) * e i0 j + (algebraMap (𝓞 E) E s) * (1 : Matrix (Fin M) (Fin M) E) i0 j := by
      intro j
      have hj := hY i0 j
      rw [Matrix.sub_apply, mul_sub] at hj
      linear_combination hj
    show (algebraMap (𝓞 E) E s) * ∑ j, Y i0 j * x j = _
    simp only [Finset.mul_sum, ← mul_assoc, hsplit, add_mul, Finset.sum_add_distrib, Matrix.one_apply,
      mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Algebra.smul_def, map_natCast]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hvec : (algebraMap (𝓞 E) E s) • Y.mulVec x = (algebraMap (𝓞 E) E s) • x +
      ∑ i, ∑ j, Pi.single i ((k : F) • (e i j * ((u : F) • x j))) := by
    funext i0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [key i0]
    congr 1
    simp only [Finset.sum_apply, Pi.single_apply]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hvec]
  exact add_mem_crdOf b L0 (algebraMap_smul_mem_crdOf b L0 s hx)
    (sum_mem_crdOf b L0 _ _ fun i _ => sum_mem_crdOf b L0 _ _ fun j _ =>
      hk i _ ((he i j).mul (hu x hx j)))

end Glob

end PI.UnitaryGroupMassFormula.UJClassMass
