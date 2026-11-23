import Development.EtaleCohomology.EtaleSheaves.LeafGhostCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CochainComplex CochainComplex.HomComplex LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.KernelLocalization

variable (R : Type) [CommRing R] (F : Shv R)

def bd {U E : Spc} (f : U ⟶ E) (m n : ℤ) (h : 1 + m = n) : H R U F m →+ Hrel R f F n :=
  HK.pre R (mappingCone.fst ((chains R).map f)) F m n h

theorem bd_pull {U E : Spc} (f : U ⟶ E) (m n : ℤ) (h : 1 + m = n) (w : H R E F m) :
    bd R F f m n h (pull R f F m w) = 0 := by
  obtain ⟨w, rfl⟩ := w.mk_surjective
  change CohomologyClass.mk (zcomp _ (zcomp (Cocycle.ofHom ((chains R).map f)) w (zero_add m)) h) = 0
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m, by omega, n.negOnePow • (mappingCone.snd ((chains R).map f)).comp w.1 (zero_add m), ?_⟩
  rw [δ_units_smul, δ_comp _ _ _ 1 n n (by omega) (by omega) (by omega), mappingCone.δ_snd]
  change _ = (mappingCone.fst ((chains R).map f)).1.comp ((Cochain.ofHom ((chains R).map f)).comp w.1 (zero_add m)) h
  have hn : n.negOnePow = - m.negOnePow := by rw [← h, add_comm, Int.negOnePow_succ]
  simp [hn, smul_smul]

theorem exists_bd {U E : Spc} (f : U ⟶ E) (m n : ℤ) (h : 1 + m = n) (z : Hrel R f F n) (hz : fgt R f F n z = 0) :
    ∃ y, bd R F f m n h y = z := by
  obtain ⟨c, rfl⟩ := z.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.inr ((chains R).map f))) c (zero_add n)) = 0 at hz
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m (by omega)] at hz
  obtain ⟨γ, hγ⟩ := hz
  change δ m n γ = (Cochain.ofHom (mappingCone.inr ((chains R).map f))).comp c.1 (zero_add n) at hγ
  let a : Cochain ((chains R).obj U) (res R F) m :=
    (mappingCone.inl ((chains R).map f)).comp c.1 (show -1 + n = m by omega) +
      m.negOnePow • (Cochain.ofHom ((chains R).map f)).comp γ (zero_add m)
  have key : (mappingCone.fst ((chains R).map f)).1.comp a h =
      c.1 - δ m n ((mappingCone.snd ((chains R).map f)).comp γ (zero_add m)) := by
    rw [δ_comp _ _ _ 1 n n (by omega) (by omega) (by omega), mappingCone.δ_snd, hγ,
      mappingCone.ext_cochain_from_iff _ m n (by omega)]
    constructor
    · simp [a]
    · simp [a]
  have ha : δ m n a = 0 := by
    have h1 := congrArg (δ n (n + 1)) key
    rw [δ_sub, δ_δ, Cocycle.δ_eq_zero, δ_comp _ _ _ 2 n (n + 1) (by omega) (by omega) (by omega),
      Cocycle.δ_eq_zero] at h1
    have h2 := congrArg (fun z => (mappingCone.inl ((chains R).map f)).comp z (show -1 + (n + 1) = n by omega)) h1
    simpa using h2
  refine ⟨CohomologyClass.mk (Cocycle.mk a n (by omega) ha), ?_⟩
  change CohomologyClass.mk (zcomp _ _ h) = _
  rw [eq_comm, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨m, by omega, (mappingCone.snd ((chains R).map f)).comp γ (zero_add m), ?_⟩
  change _ = c.1 - (mappingCone.fst ((chains R).map f)).1.comp a h
  rw [key]; abel

theorem range_of_bd {U E : Spc} (f : U ⟶ E) (m n : ℤ) (h : 1 + m = n) (y : H R U F m) (hy : bd R F f m n h y = 0) :
    ∃ w, pull R f F m w = y := by
  obtain ⟨y, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp _ y h) = 0 at hy
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m (by omega)] at hy
  obtain ⟨β, hβ⟩ := hy
  change δ m n β = (mappingCone.fst ((chains R).map f)).1.comp y.1 h at hβ
  have hw : δ m n (-(m.negOnePow • (Cochain.ofHom (mappingCone.inr ((chains R).map f))).comp β (zero_add m))) = 0 := by
    rw [δ_neg, δ_units_smul, δ_ofHom_comp, hβ]; simp
  refine ⟨CohomologyClass.mk (Cocycle.mk _ n (by omega) hw), ?_⟩
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) _ (zero_add m)) = _
  rw [eq_comm, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨m - 1, by omega, (mappingCone.inl ((chains R).map f)).comp β (by omega), ?_⟩
  rw [δ_comp _ _ _ 0 n m (by omega) (by omega) (by omega), mappingCone.δ_inl, hβ]
  change _ = y.1 - (Cochain.ofHom ((chains R).map f)).comp _ (zero_add m)
  simp [Cochain.ofHom_comp]

theorem rpull_bd {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f)
    (m n : ℤ) (h : 1 + m = n) (y : H R U F m) :
    rpull R f f' u e comm F n (bd R F f m n h y) = bd R F f' m n h (pull R u F m y) := by
  obtain ⟨y, rfl⟩ := y.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  change (Cochain.ofHom (rmap R f f' u e comm)).comp ((mappingCone.fst ((chains R).map f)).1.comp y.1 h) (zero_add n) =
    (mappingCone.fst ((chains R).map f')).1.comp ((Cochain.ofHom ((chains R).map u)).comp y.1 (zero_add m)) h
  rw [mappingCone.ext_cochain_from_iff _ m n (by omega)]
  constructor
  · rw [← Cochain.comp_assoc_of_second_is_zero_cochain]
    simp [rmap, mappingCone.map]
  · rw [← Cochain.comp_assoc_of_first_is_zero_cochain]
    simp [rmap, mappingCone.map]

theorem rpull_comp {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'') (u : U' ⟶ U) (e : E' ⟶ E)
    (comm : f' ≫ e = u ≫ f) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (comm' : f'' ≫ e' = u' ≫ f') (u2 : U'' ⟶ U) (e2 : E'' ⟶ E)
    (comm2 : f'' ≫ e2 = u2 ≫ f) (hu : u2 = u' ≫ u) (he : e2 = e' ≫ e) (n : ℤ) (z : Hrel R f F n) :
    rpull R f f'' u2 e2 comm2 F n z = rpull R f' f'' u' e' comm' F n (rpull R f f' u e comm F n z) := by
  subst hu he
  have key : rmap R f f'' (u' ≫ u) (e' ≫ e) comm2 = rmap R f' f'' u' e' comm' ≫ rmap R f f' u e comm := by
    simp only [rmap, Functor.map_comp]
    exact mappingCone.map_comp ..
  obtain ⟨z, rfl⟩ := z.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, key, Cochain.ofHom_comp]

end LateralTheory.E.KernelLocalization
