import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.TranslGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.TranslDD
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.AdExExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.EvIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.GaloisLiftMemFirstOrderDeformations
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.PolZCases
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.AdicLC
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L}

private theorem char_K (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] [Algebra ℤ_[l] K] : (l : K) = 0 := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have hpp : p.Prime := CharP.char_is_prime K p
  by_cases e : p = l
  · subst e; exact CharP.cast_eq_zero K p
  · have hc : l.Coprime p := (Nat.coprime_primes Fact.out hpp).2 (Ne.symm e)
    have := (PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hc)).map (algebraMap ℤ_[l] K)
    rw [map_natCast, CharP.cast_eq_zero] at this
    exact absurd this not_isUnit_zero

private theorem two_unit {A : Type} [CommRing A] (hl : l ≠ 2) (h : (l : A) = 0) : IsUnit (2 : A) := by
  obtain ⟨s, hs⟩ := (Fact.out : l.Prime).odd_of_ne_two hl
  refine IsUnit.of_mul_eq_one (-(s : A)) ?_
  rw [hs] at h
  push_cast at h
  linear_combination -h

private theorem cases_G (γ : G.Γ) : ∃ g : G.G₀, γ = g ∨ γ = g * G.c := by
  by_cases h : γ ∈ G.η.ker
  · exact ⟨⟨γ, h⟩, Or.inl rfl⟩
  · refine ⟨⟨γ * G.c, ?_⟩, Or.inr (by simp only [mul_assoc, G.c_sq, mul_one])⟩
    rw [MonoidHom.mem_ker] at h ⊢
    rw [map_mul, G.η_c, (Int.units_eq_one_or (G.η γ)).resolve_left h]
    simp

private theorem cont_rep {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] [TopologicalSpace M]
    [DiscreteTopology M] (ρ : Representation A G.Γ M) (hk : ∀ᶠ g : G.G₀ in nhds 1, ∀ m, ρ g m = m) :
    ContAction ρ := by
  have e3 : Filter.map (Subtype.val : G.G₀ → G.Γ) (nhds 1) = nhds 1 :=
    G.η_open.isOpenEmbedding_subtypeVal.map_nhds_eq 1
  have hk' : ∀ᶠ g : G.Γ in nhds 1, ∀ m, ρ g m = m := by rw [← e3, eventually_map]; exact hk
  refine continuous_prod_of_discrete_right.2 fun m => ?_
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun g0 => ?_)
  have hc : Tendsto (fun g => g0⁻¹ * g) (nhds g0) (nhds 1) := by
    have : Continuous fun g : G.Γ => g0⁻¹ * g := by fun_prop
    simpa using this.tendsto g0
  filter_upwards [hc.eventually hk'] with g hg
  have : g = g0 * (g0⁻¹ * g) := by simp
  show ρ g m = ρ g0 m
  rw [this, map_mul, Module.End.mul_apply, hg]

private theorem lc_pi {Γ R ι : Type} [TopologicalSpace Γ] [Finite ι] (f : Γ → ι → R)
    (h : ∀ i, IsLocallyConstant fun g => f g i) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  filter_upwards [Filter.eventually_all.2 fun i => (h i).eventually_eq g0] with g hg
  exact funext hg

variable {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} (k : Kap x) {X : Type} [CommRing X] [Algebra x.A X]
  {D : Dat x.A (plOf G)}

private noncomputable def iota (o : IsOd h x X D) : D.M.X →ₗ[x.A] W2 n x.A X k.g x.a where
  toFun m := ⟨mk2 (fun _ => 0) (o.e m), evenOddBlockMatrix_mem_adjointDeformSubspace (fun _ => zero_mem _) (o.e m).2⟩
  map_add' a b := Subtype.ext (by simp [epsPrimeEtaMatrix_add])
  map_smul' c a := Subtype.ext (by simp [epsPrimeEtaMatrix_smul])

private theorem iota_val (o : IsOd h x X D) (m) :
    (iota k o m : Matrix (Fin n) (Fin n) (DD X k.g)) = mk2 (fun _ => 0) (o.e m) := rfl

private theorem iota_inj (o : IsOd h x X D) : Function.Injective (iota k o) := fun _ _ e =>
  o.e.injective (Subtype.ext (epsPrimeEtaMatrix_injective_pair (congrArg Subtype.val e)).2)

private theorem iota_range (o : IsOd h x X D) (M : W2 n x.A X k.g x.a) (Z)
    (e : (M : Matrix (Fin n) (Fin n) (DD X k.g)) = mk2 (fun _ => 0) Z) : M ∈ LinearMap.range (iota k o) := by
  obtain ⟨P, Z', -, hZ, e'⟩ := exists_evenOddBlock_decomposition_of_mem M.2
  refine ⟨o.e.symm ⟨Z', hZ⟩, Subtype.ext ?_⟩
  rw [iota_val, LinearEquiv.apply_symm_apply, e, (epsPrimeEtaMatrix_injective_pair (e.symm.trans e')).2]

private def triN (v : L.Vl) : Submodule x.A (W2 n x.A X k.g x.a) where
  carrier := {Z | (k.wi1 X v * (Z : Matrix (Fin n) (Fin n) (DD X k.g)) * k.w1 X v).BlockTriangular id}
  zero_mem' := by
    intro i j _
    simp
  add_mem' := by
    intro Z Z' h h' i j hij
    have e1 := h hij
    have e2 := h' hij
    simp only [Submodule.coe_add, mul_add, add_mul, Matrix.add_apply, e1, e2, add_zero]
  smul_mem' := by
    intro c Z h i j hij
    have e1 := h hij
    simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, e1, smul_zero]

private theorem triN_iff (v : L.Vl) (M : W2 n x.A X k.g x.a) :
    M ∈ triN k v ↔ ∀ i j, j < i → (k.wi1 X v * (M : Matrix (Fin n) (Fin n) (DD X k.g)) * k.w1 X v) i j = 0 :=
  ⟨fun h _ _ e => h e, fun h i j e => h i j e⟩

private theorem triN_conj (v : L.Vl) (g : L.Gv v) (M M' : W2 n x.A X k.g x.a) (hM : M ∈ triN k v)
    (e : (M' : Matrix (Fin n) (Fin n) (DD X k.g)) = k.ρ1 X (G0.φ v g) * M * k.ρ1 X (G0.φ v g⁻¹)) : M' ∈ triN k v := by
  show (k.wi1 X v * (M' : Matrix (Fin n) (Fin n) (DD X k.g)) * k.w1 X v).BlockTriangular id
  have t : ∀ g : L.Gv v, (k.wi1 X v * k.ρ1 X (G0.φ v g) * k.w1 X v).BlockTriangular id := fun g i j e =>
    ((tri l G0.frame n x k X v).1 g).1 i j e
  have e2 : ∀ P Q Z : Matrix (Fin n) (Fin n) (DD X k.g), k.wi1 X v * (P * Z * Q) * k.w1 X v =
      (k.wi1 X v * P * k.w1 X v) * (k.wi1 X v * Z * k.w1 X v) * (k.wi1 X v * Q * k.w1 X v) := by
    intro P Q Z
    simp only [Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc (k.w1 X v) (k.wi1 X v), ((rho1 l G0.frame n x k X).2.2.2.1 v).2, Matrix.one_mul]
  rw [e, e2]
  exact ((t g).mul hM).mul (t g⁻¹)

private theorem sum_smul_block_matrix {ι : Type} (s : Finset ι) (c : ι → x.A) (P : ι → Fin k.g → Matrix (Fin n) (Fin n) X)
    (Z : ι → Matrix (Fin n) (Fin n) X) :
    ∑ i ∈ s, c i • mk2 (P i) (Z i) = mk2 (fun j => ∑ i ∈ s, c i • P i j) (∑ i ∈ s, c i • Z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Matrix.ext fun _ _ => rfl
  | insert i s hi ih => simp only [Finset.sum_insert hi]; rw [ih, epsPrimeEtaMatrix_smul, epsPrimeEtaMatrix_add]

private theorem diag0 (v : L.Vl) (E : W2 n x.A X k.g x.a) {P Z} (i : Fin n)
    (e : (E : Matrix (Fin n) (Fin n) (DD X k.g)) = mk2 P Z) (hP : ∀ j, (x.wiX X v * P j * x.wX X v) i i = 0) :
    (k.wi1 X v * (E : Matrix (Fin n) (Fin n) (DD X k.g)) * k.w1 X v) i i = 0 := by
  obtain ⟨P', Z', hP', hZ, e5⟩ := exists_evenOddBlock_decomposition_of_mem E.2
  obtain ⟨rfl, rfl⟩ := epsPrimeEtaMatrix_injective_pair (e5.symm.trans e)
  rw [e5, weyl_conj_block_matrix, epsPrimeEtaMatrix_apply_eq_zero_iff]
  exact ⟨hP, od_diag (x := x) X v (add_mem hZ (cmm_mem k X v hP')) i⟩

private theorem fixV (o : IsOd h x X D) (v : L.Vl) (E : W2 n x.A X k.g x.a) {P Z}
    (e : (E : Matrix (Fin n) (Fin n) (DD X k.g)) = mk2 P Z)
    (hP : ∀ j a b, b < a → (x.wiX X v * P j * x.wX X v) a b = 0) : ∃ m, E - iota k o m ∈ triN k v := by
  obtain ⟨P', Z', hP', hZ, e5⟩ := exists_evenOddBlock_decomposition_of_mem E.2
  obtain ⟨rfl, rfl⟩ := epsPrimeEtaMatrix_injective_pair (e5.symm.trans e)
  refine ⟨o.e.symm ⟨Z' + cmm k X v P', add_mem hZ (cmm_mem k X v hP')⟩, (triN_iff k v _).2 fun a b hab => ?_⟩
  rw [Submodule.coe_sub, iota_val, LinearEquiv.apply_symm_apply, e5, epsPrimeEtaMatrix_sub, weyl_conj_block_matrix, epsPrimeEtaMatrix_apply_eq_zero_iff]
  simp only [sub_zero]
  exact ⟨fun j => hP j a b hab, by simp⟩

private theorem kerV' (o : IsOd h x X D) (v : L.Vl) (m') : D.π (.inl v) m' = 0 ↔ iota k o m' ∈ triN k v := by
  refine (o.kerV v m').trans (Iff.trans ?_ (triN_iff k v _).symm)
  simp only [iota_val, weyl_conj_block_matrix, epsPrimeEtaMatrix_apply_eq_zero_iff, cmm, mul_zero, zero_mul, sub_self, Finset.sum_const_zero,
    add_zero, Matrix.zero_apply, implies_true, true_and]

private theorem sum_diag {A X ι : Type} [CommRing A] [CommRing X] [Algebra A X] [Fintype ι] {n : ℕ} (c : ι → A)
    (a b : Matrix (Fin n) (Fin n) X) (P : ι → Matrix (Fin n) (Fin n) X) (i : Fin n)
    (h : ∀ s, (a * P s * b) i i = 0) : (a * (∑ s, c s • P s + 0) * b) i i = 0 := by
  simp only [add_zero, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.sum_apply,
    Matrix.smul_apply, h, smul_zero, Finset.sum_const_zero]

end SlopeTestRemainingChoices

set_option maxHeartbeats 300000 in
theorem UpperTheory.V.Pa.B2.transl :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X] [Finite X] (D : Dat x.A (plOf G)) (e : ℕ) (z : Fin e → Fin k.g → G.G₀ → Matrix (Fin n) (Fin n) X), l ≠ 2 → (∃ m : ℕ, algebraMap x.A X (x.t ^ m) = 0) → IsOd h x X D → (∀ u, UrAx l (L.Ju u)) → (∀ i j, z i j ∈ SelP h x X) → ∃ ξ : Fin e → D.selmerSecondCocycles, ∀ c : Fin e → x.A, ((∑ i, c i • ξ i : D.selmerSecondCocycles) : D.C2) ∈ D.selmerSecondCoboundaries → ∃ Ψ ∈ Sel2 h X k, ∀ j γ a b, (Ψ γ a b).ep' j = (∑ i, c i • z i j γ) a b := by
  rintro l _ L G G0 h n x k X _ _ _ D e z hl ⟨m, hm⟩ o hur hz
  have hA : (l : x.A) = 0 := by rw [← map_natCast (algebraMap x.K x.A), char_K l x.K, map_zero]
  obtain ⟨rep, had⟩ := adEx l G.frame x.A _ n _ _ _ (ok1 l L G G0 h n x k X 1).2.2
  obtain ⟨repE, hadE⟩ := adEx l G.frame x.A X n _ _ _ (okX l L G G0 h n x X 1).1
  have ha : ∀ (g : G.G₀) (Z : W2 n x.A X k.g x.a), (rep g Z : Matrix (Fin n) (Fin n) (DD X k.g)) =
      k.ρ1 X (h.p₀ g) * Z * k.ρ1 X (h.p₀ g⁻¹) := fun g Z => by
    simpa only [MonoidHom.one_apply, map_one, one_smul] using had.1 g Z
  have hc : ∀ Z : W2 n x.A X k.g x.a, (rep G.c Z : Matrix (Fin n) (Fin n) (DD X k.g)) =
      -(Z : Matrix (Fin n) (Fin n) (DD X k.g))ᵀ := fun Z => by
    simpa only [MonoidHom.one_apply, map_one, one_smul] using had.2 Z
  have haE : ∀ (g : G.G₀) (Z : Ev x.A X n x.a), (repE g Z : Matrix (Fin n) (Fin n) X) =
      x.ρX X (h.p₀ g) * Z * x.ρX X (h.p₀ g⁻¹) := fun g Z => by
    simpa only [MonoidHom.one_apply, map_one, one_smul] using hadE.1 g Z
  have hcE : ∀ Z : Ev x.A X n x.a, (repE G.c Z : Matrix (Fin n) (Fin n) X) = -(Z : Matrix (Fin n) (Fin n) X)ᵀ :=
    fun Z => by simpa only [MonoidHom.one_apply, map_one, one_smul] using hadE.2 Z
  have hp : Continuous h.p₀ := (h.cont.comp continuous_subtype_val).subtype_mk _
  have hφ : ∀ v g, h.p₀ (G.φ v g) = G0.φ v g := fun v g => Subtype.ext (h.φ v g)
  have hφu : ∀ v g, h.p₀ (G.φu v g) = G0.φu v g := fun v g => Subtype.ext (h.φu v g)
  obtain ⟨r1, -, -, -, r5⟩ := rho1 l G0.frame n x k X
  letI : TopologicalSpace (W2 n x.A X k.g x.a) := ⊥
  haveI : DiscreteTopology (W2 n x.A X k.g x.a) := ⟨rfl⟩
  haveI : Finite (DD X k.g) := Finite.of_equiv _ DD.equiv.symm
  have hcont : ContAction rep := by
    refine cont_rep rep ?_
    filter_upwards [((isLocallyConstant_rho1_of_algebraMap_pow_eq_zero k X m hm).comp_continuous hp).eventually_eq 1,
      ((isLocallyConstant_rho1_of_algebraMap_pow_eq_zero k X m hm).comp_continuous (hp.comp continuous_inv)).eventually_eq 1] with g h1 h2 Z
    apply Subtype.ext
    simp only [Function.comp, inv_one, map_one, r1] at h1 h2
    rw [ha, h1, h2, one_mul, mul_one]
  let M : FRep x.A G.Γ := { X := W2 n x.A X k.g x.a, ρ := rep, cont := hcont }
  have he : ∀ γ m, iota k o (D.M.ρ γ m) = rep γ (iota k o m) := by
    have e1 : ∀ (g : G.G₀) m, iota k o (D.M.ρ g m) = rep g (iota k o m) := fun g m =>
      Subtype.ext (by rw [ha, iota_val, iota_val, o.act, rho1_conj_block_zero])
    have e2 : ∀ m, iota k o (D.M.ρ G.c m) = rep G.c (iota k o m) := fun m =>
      Subtype.ext (by rw [hc, iota_val, iota_val, o.actc, neg_transpose_epsPrimeEtaMatrix]; simp)
    intro γ m
    obtain ⟨g, rfl | rfl⟩ := cases_G γ
    · exact e1 g m
    · rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e1, e2]
  have eqv : ∀ γ (Mx : W2 n x.A X k.g x.a) (P : Fin k.g → Ev x.A X n x.a) Z,
      (Mx : Matrix (Fin n) (Fin n) (DD X k.g)) = mk2 (fun j => P j) Z →
      ∃ Z', (rep γ Mx : Matrix (Fin n) (Fin n) (DD X k.g)) = mk2 (fun j => repE γ (P j)) Z' := by
    have e1 : ∀ (γ : G.G₀) (Mx : W2 n x.A X k.g x.a) (P : Fin k.g → Ev x.A X n x.a) Z,
        (Mx : Matrix (Fin n) (Fin n) (DD X k.g)) = mk2 (fun j => P j) Z →
        ∃ Z', (rep γ Mx : Matrix (Fin n) (Fin n) (DD X k.g)) = mk2 (fun j => repE γ (P j)) Z' := by
      intro γ Mx P Z e
      simp only [ha, haE, e]
      exact rho1_conj_block_matrix k X _ _ _ _
    intro γ Mx P Z e
    obtain ⟨g, rfl | rfl⟩ := cases_G γ
    · exact e1 g Mx P Z e
    · simp only [map_mul, Module.End.mul_apply]
      exact e1 g _ (fun j => repE G.c (P j)) _ (by simp only [hc, hcE, e, neg_transpose_epsPrimeEtaMatrix]; rfl)
  have hy : ∀ i j, ∃ y ∈ Zl repE, y G.c = 0 ∧ ∀ g : G.G₀, (y g : Matrix (Fin n) (Fin n) X) = z i j g := by
    intro i j
    obtain ⟨a1, a2, a3, a4, -, -⟩ := hz i j
    refine (polZ l G.frame x.A X n _ _ _ repE hadE).1 (z i j) a1
      (lc_pi _ fun a => lc_pi _ fun b => (adicLC _ _ _ m _ (by rw [← map_pow, hm])).1 (a2 a b))
      (fun g g' => by simpa only [MonoidHom.one_apply, map_one, one_smul] using a3 g g')
      (fun g => by simpa only [MonoidHom.one_apply, map_one, one_smul] using a4 g)
  choose y hy1 hy2 hy3 using hy
  choose Y hY1 hY2 using fun i j v => (hz i j).2.2.2.2.2 v
  let sec : (Fin k.g → Ev x.A X n x.a) → W2 n x.A X k.g x.a := fun P =>
    ⟨mk2 (fun j => P j) 0, evenOddBlockMatrix_mem_adjointDeformSubspace (fun j => (P j).2) (zero_mem _)⟩
  let xs : Fin e → G.Γ → W2 n x.A X k.g x.a := fun i γ => sec fun j => y i j γ
  have hxs : ∀ i, Continuous (xs i) := fun i =>
    ((lc_pi (fun γ j => y i j γ) fun j => (hy1 i j).1).comp sec).continuous
  have hd : ∀ i s, d1 M.ρ (xs i) s ∈ LinearMap.range (iota k o) := by
    rintro i ⟨g, g'⟩
    obtain ⟨Z', e⟩ := eqv g (xs i g') _ _ rfl
    refine iota_range k o _ (Z' - 0 + 0) ?_
    show ((rep g (xs i g') : Matrix (Fin n) (Fin n) (DD X k.g)) - mk2 (fun j => y i j (g * g')) 0 +
      mk2 (fun j => y i j g) 0) = _
    rw [e, epsPrimeEtaMatrix_sub, epsPrimeEtaMatrix_add]
    congr 1
    funext j
    rw [(hy1 i j).2, Submodule.coe_add]
    abel
  let Ys : Fin e → L.Vl → W2 n x.A X k.g x.a := fun i v => sec fun j => ⟨Y i j v, hY1 i j v⟩
  have hJ : ∀ u, ∀ g ∈ L.Ju u, ∀ Z, rep (G.φu u g) Z = Z := fun u g hg Z => Subtype.ext (by
    rw [ha, ← map_inv, hφu, hφu, r5 u _ ⟨g, hg, rfl⟩, r5 u _ ⟨g⁻¹, inv_mem hg, rfl⟩, one_mul, mul_one])
  have hU : ∀ i u, ∃ b : L.Gu u → W2 n x.A X k.g x.a, (Continuous b ∧
      ∀ g g', b (g * g') = b g + rep (G.φu u g) (b g')) ∧ (∀ g ∈ L.Ju u, b g = 0) ∧
      ∀ g, xs i (G.φu u g) - b g ∈ LinearMap.range (iota k o) := by
    intro i u
    have cφ : Continuous fun g => (G.φu u g : G.Γ) := continuous_subtype_val.comp (G.φu_cont u)
    refine urLift (hur u) { X := W2 n x.A X k.g x.a, ρ := rep.comp (G.η.ker.subtype.comp (G.φu u))
                            cont := hcont.comp (cφ.prodMap continuous_id) }
      (fun m => by rw [← Nat.cast_smul_eq_nsmul x.A, hA, zero_smul]) (hJ u) (LinearMap.range (iota k o)) ?_
      (fun g => xs i (G.φu u g)) ((hxs i).comp cφ) ?_ fun g hg => iota_range k o _ 0 ?_
    · rintro g _ ⟨m, rfl⟩
      exact ⟨_, he _ m⟩
    · rintro ⟨g, g'⟩
      have := hd i (G.φu u g, G.φu u g')
      rw [d1_apply, ← Subgroup.coe_mul, ← map_mul] at this
      exact this
    · show mk2 (fun j => (y i j (G.φu u g) : Matrix (Fin n) (Fin n) X)) 0 = _
      simp only [hy3, fun j => (hz i j).2.2.2.2.1 u _ ⟨g, hg, rfl⟩]
  choose bU hb1 hb2 hb3 using hU
  have hV : ∀ i v (g : L.Gv v), ∃ Z, ((xs i (G.φ v g) - (rep (G.φ v g) (Ys i v) - Ys i v) : W2 n x.A X k.g x.a) :
      Matrix (Fin n) (Fin n) (DD X k.g)) =
      mk2 (fun j => z i j (G.φ v g) - dY G.frame (fun g => x.ρX X (h.p₀ g)) (Y i j v) (G.φ v g)) Z := by
    intro i v g
    obtain ⟨Z', e⟩ := eqv (G.φ v g) (Ys i v) _ _ rfl
    refine ⟨0 - (Z' - 0), ?_⟩
    show mk2 (fun j => y i j (G.φ v g)) 0 - ((rep (G.φ v g) (Ys i v) : Matrix (Fin n) (Fin n) (DD X k.g)) -
      mk2 (fun j => Y i j v) 0) = _
    rw [e, epsPrimeEtaMatrix_sub, epsPrimeEtaMatrix_sub]
    simp only [hy3, haE, dY]
  let N : (plOf G).ι → Submodule x.A M.X := fun w => match w with
    | .inl v => triN k v
    | .inr _ => ⊥
  let b : Fin e → ∀ w, (plOf G).G w → M.X := fun i w => match w with
    | .inl v => fun g : L.Gv v => rep (G.φ v g) (Ys i v) - Ys i v
    | .inr u => bU i u
  refine (translGen D M (iota k o) (iota_inj k o) he N ?_ ?_ G.c G.c_sq (two_unit hl hA) xs hxs hd
    (fun i => iota_range k o _ 0 (by
      show mk2 (fun j => (y i j G.c : Matrix (Fin n) (Fin n) X)) 0 = _
      simp only [hy2, ZeroMemClass.coe_zero])) b ?_ ?_ ?_).imp fun ξ hξ c hB => ?main
  case main =>
    obtain ⟨Ψ, h1, h2, h3, h4⟩ := hξ c hB
    have lcΨ : IsLocallyConstant Ψ := (IsLocallyConstant.iff_continuous _).2 h1.1
    have h5 : ∀ g : G.G₀, ∃ Z, ((Ψ g : W2 n x.A X k.g x.a) : Matrix (Fin n) (Fin n) (DD X k.g)) =
        mk2 (fun j => ∑ i, c i • z i j g) Z := by
      intro g
      obtain ⟨m', hm'⟩ := h3 g
      have e1 : (Ψ g : W2 n x.A X k.g x.a) = ∑ i, c i • xs i g + iota k o m' := by
        rw [hm']; exact (add_sub_cancel _ _).symm
      rw [e1, Submodule.coe_add, Submodule.coe_sum, iota_val]
      simp only [Submodule.coe_smul, xs, sec, hy3]
      rw [sum_smul_block_matrix, epsPrimeEtaMatrix_add]
      simp only [add_zero]
      exact ⟨_, rfl⟩
    refine ⟨fun g => (Ψ g : W2 n x.A X k.g x.a), ⟨fun g => (Ψ g).2, fun a b => ?_, fun g g' => ?_, fun g => ?_,
      ?_, fun v => ?_⟩, fun j γ a b => ?_⟩
    · exact fun s => (lcΨ.comp_continuous continuous_subtype_val).comp fun Z : W2 n x.A X k.g x.a =>
        Ideal.Quotient.mk _ ((Z : Matrix (Fin n) (Fin n) (DD X k.g)) a b)
    · exact (congrArg Subtype.val (h1.2 g g')).trans (congrArg (_ + ·) (ha g _))
    · simpa only [MonoidHom.one_apply, map_one, one_smul] using
        ((polZ l G.frame x.A _ n _ _ _ rep had).2 Ψ ⟨lcΨ, h1.2⟩ h2).1 g
    · rintro u _ ⟨g, hg, rfl⟩
      obtain ⟨m', hm'⟩ := h4 (.inr u)
      have e1 : (Ψ (G.φu u g) : W2 n x.A X k.g x.a) - ∑ i, c i • bU i u g -
        (rep (G.φu u g) (iota k o m') - iota k o m') = 0 := hm' g hg
      simp only [hJ u g hg, fun i => hb2 i u g hg, smul_zero, Finset.sum_const_zero, sub_self, sub_zero] at e1
      exact congrArg Subtype.val e1
    · obtain ⟨m', hm'⟩ := h4 (.inl v)
      refine ⟨(∑ i, c i • Ys i v + iota k o m' : W2 n x.A X k.g x.a), Subtype.prop _, fun g => ?_⟩
      have e1 : (Ψ (G.φ v g) : W2 n x.A X k.g x.a) - ∑ i, c i • (rep (G.φ v g) (Ys i v) - Ys i v) -
        (rep (G.φ v g) (iota k o m') - iota k o m') ∈ triN k v := hm' g trivial
      generalize hE : (Ψ (G.φ v g) : W2 n x.A X k.g x.a) - ∑ i, c i • (rep (G.φ v g) (Ys i v) - Ys i v) -
        (rep (G.φ v g) (iota k o m') - iota k o m') = E at e1
      have e2 : ((Ψ (G.φ v g) : W2 n x.A X k.g x.a) : Matrix (Fin n) (Fin n) (DD X k.g)) -
          dY G.frame (fun g => k.ρ1 X (h.p₀ g)) (∑ i, c i • Ys i v + iota k o m' : W2 n x.A X k.g x.a) (G.φ v g) = E := by
        rw [dY, ← ha, ← Submodule.coe_sub, ← Submodule.coe_sub, ← hE]
        congr 1
        simp only [map_add, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
        abel
      show (∀ i j, j < i → (k.wi1 X v * (((Ψ (G.φ v g) : W2 n x.A X k.g x.a) : Matrix (Fin n) (Fin n) (DD X k.g)) - _) *
        k.w1 X v) i j = 0) ∧ (_ → ∀ i, (k.wi1 X v * (((Ψ (G.φ v g) : W2 n x.A X k.g x.a) :
          Matrix (Fin n) (Fin n) (DD X k.g)) - _) * k.w1 X v) i i = 0)
      erw [e2]
      refine ⟨(triN_iff k v E).1 e1, fun hg i => ?_⟩
      obtain ⟨m2, hm2⟩ := h3 (G.φ v g)
      have e3 : E = ∑ i, c i • (xs i (G.φ v g) - (rep (G.φ v g) (Ys i v) - Ys i v)) +
          iota k o (m2 - (D.M.ρ (G.φ v g) m' - m')) := by
        rw [← hE, map_sub, map_sub, he, hm2]
        simp only [smul_sub, Finset.sum_sub_distrib]
        abel
      choose Zv hZv using fun i => hV i v g
      have e4 := congrArg Subtype.val e3
      rw [Submodule.coe_add, Submodule.coe_sum, iota_val] at e4
      simp only [Submodule.coe_smul, hZv] at e4
      rw [sum_smul_block_matrix, epsPrimeEtaMatrix_add] at e4
      exact diag0 k v E i e4 fun j => sum_diag c _ _ _ i fun s => (hY2 s j v g).2 hg i
    · obtain ⟨Z, e1⟩ := h5 γ
      beta_reduce
      rw [e1]
      rfl
  · rintro (v | u)
    · intro (g : L.Gv v) Z hZ
      exact triN_conj k v g Z _ hZ ((ha (G.φ v g) Z).trans
        (congrArg₂ (fun s t => k.ρ1 X s * (Z : W2 n x.A X k.g x.a).1 * k.ρ1 X t) (hφ v g)
          ((congrArg h.p₀ ((G.φ v).map_inv g).symm).trans (hφ v _))))
    · intro g Z hZ
      rw [(Submodule.mem_bot _).1 hZ, map_zero]
      exact zero_mem _
  · rintro (v | u) m'
    · exact kerV' k o v m'
    · exact (map_eq_zero_iff _ (o.kerU u)).trans
        ((map_eq_zero_iff _ (iota_inj k o)).symm.trans (Submodule.mem_bot _).symm)
  · rintro i (v | u)
    · exact (hcont.comp ((continuous_subtype_val.comp (G.φ_cont v)).prodMk continuous_const)).sub continuous_const
    · exact (hb1 i u).1
  · rintro i (v | u)
    · intro (g : L.Gv v) (g' : L.Gv v)
      show rep (G.φ v (g * g')) (Ys i v) - Ys i v = rep (G.φ v g) (Ys i v) - Ys i v +
        rep (G.φ v g) (rep (G.φ v g') (Ys i v) - Ys i v)
      rw [map_mul, Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_sub]
      abel
    · exact (hb1 i u).2
  · rintro i (v | u)
    · intro (g : L.Gv v)
      obtain ⟨Z, e1⟩ := hV i v g
      exact fixV k o v _ e1 fun j => (hY2 i j v g).1
    · intro (g : L.Gu u)
      obtain ⟨m', hm'⟩ := hb3 i u g
      exact ⟨m', (Submodule.mem_bot _).2 (sub_eq_zero.2 hm'.symm)⟩
