import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ScalingExistence.ExistsScale

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc Matrix

namespace UpperTheory.V.Z.Sym.Loc.FU

private def Bd (O : Type) [CommRing O] {ι A : Type} [CommRing A] [Algebra O A] (f : ι → A) : Prop :=
  ∃ N : O, N ≠ 0 ∧ ∀ i, IsIntegral O (N • f i)

section Bd

variable {O : Type} [CommRing O] [IsDomain O] {ι A B : Type} [CommRing A] [Algebra O A] [CommRing B] [Algebra O B]
  {f g : ι → A}

private theorem Bd.of_int (h : ∀ i, IsIntegral O (f i)) : Bd O f := ⟨1, one_ne_zero, fun i => by simpa using h i⟩

private theorem Bd.add (hf : Bd O f) (hg : Bd O g) : Bd O fun i => f i + g i := by
  obtain ⟨M, hM, hf⟩ := hf
  obtain ⟨N, hN, hg⟩ := hg
  refine ⟨M * N, mul_ne_zero hM hN, fun i => ?_⟩
  have : (M * N) • (f i + g i) = N • M • f i + M • N • g i := by rw [smul_add, smul_smul, smul_smul, mul_comm N M]
  rw [this]; exact ((hf i).smul N).add ((hg i).smul M)

private theorem Bd.mul (hf : Bd O f) (hg : Bd O g) : Bd O fun i => f i * g i := by
  obtain ⟨M, hM, hf⟩ := hf
  obtain ⟨N, hN, hg⟩ := hg
  refine ⟨M * N, mul_ne_zero hM hN, fun i => ?_⟩
  rw [← smul_mul_smul_comm]; exact (hf i).mul (hg i)

omit [IsDomain O] in
private theorem Bd.congr (hf : Bd O f) (h : ∀ i, g i = f i) : Bd O g := by
  rw [funext h]; exact hf

omit [IsDomain O] in
private theorem Bd.map (hf : Bd O f) (φ : A →ₐ[O] B) : Bd O fun i => φ (f i) := by
  obtain ⟨M, hM, hf⟩ := hf
  exact ⟨M, hM, fun i => by rw [← map_smul]; exact (hf i).map φ⟩

omit [IsDomain O] in
private theorem Bd.of_map (φ : A →ₐ[O] B) (hφ : Function.Injective φ) (hf : Bd O fun i => φ (f i)) : Bd O f := by
  obtain ⟨M, hM, hf⟩ := hf
  exact ⟨M, hM, fun i => (isIntegral_algHom_iff φ hφ).1 (by rw [map_smul]; exact hf i)⟩

omit [IsDomain O] in
private theorem Bd.comp {κ : Type} (hf : Bd O f) (r : κ → ι) : Bd O fun i => f (r i) := by
  obtain ⟨M, hM, hf⟩ := hf
  exact ⟨M, hM, fun i => hf _⟩

omit [IsDomain O] in
private theorem Bd.of_sq (hf : Bd O fun i => f i * f i) : Bd O f := by
  obtain ⟨M, hM, hf⟩ := hf
  refine ⟨M, hM, fun i => IsIntegral.of_pow two_pos ?_⟩
  have : (M • f i) ^ 2 = M • M • (f i * f i) := by rw [pow_two, smul_mul_smul_comm, smul_smul]
  rw [this]; exact (hf i).smul M

private theorem Bd.const (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] [Algebra K A] [IsScalarTower O K A]
    [Module.Finite K A] (a : A) : Bd O fun _ : ι => a := by
  have h1 : IsAlgebraic K a := (Algebra.IsIntegral.isIntegral a).isAlgebraic
  obtain ⟨N, hN, h⟩ := ((IsFractionRing.isAlgebraic_iff O K A).2 h1).exists_integral_multiple
  exact ⟨N, hN, fun _ => h⟩

private theorem Bd.cancel (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] [Algebra K A] [IsScalarTower O K A]
    [Module.Finite K A] {u : A} (hu : IsUnit u) (hf : Bd O fun i => u * f i) : Bd O f := by
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  exact ((Bd.const K v).mul hf).congr fun i => by rw [← mul_assoc, hv, one_mul]

omit [IsDomain O] in
private theorem Bd.star {R : Type} [CommRing R] [Algebra O R] {a b : R} {f : ι → QuadraticAlgebra R a b} (hf : Bd O f) :
    Bd O fun i => star (f i) := by
  obtain ⟨M, hM, hf⟩ := hf
  refine ⟨M, hM, fun i => ?_⟩
  convert isIntegral_star_quad (hf i) using 1
  ext <;> simp

private theorem Bd.fin {κ : Type} [Finite κ] {F : κ → ι → A} (h : ∀ k, Bd O (F k)) : Bd O fun p : κ × ι => F p.1 p.2 := by
  classical
  haveI := Fintype.ofFinite κ
  choose N hN hF using h
  refine ⟨∏ k, N k, Finset.prod_ne_zero_iff.2 fun k _ => hN k, fun p => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ p.1), mul_smul]
  exact (hF p.1 p.2).smul _

end Bd

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K} {ι : Type}

private instance : Module.Finite K (EL Δ τ) := Module.Finite.trans (Lsq K Δ) (EL Δ τ)

private theorem sg_mul (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by
  ext <;> simp [sigL] <;> ring

private theorem sg_sg (x : EL Δ τ) : sigL (sigL x) = x := by
  ext <;> simp [sigL]

private theorem sg_star (x : EL Δ τ) : sigL (star x) = star (sigL x) := by
  ext <;> simp [sigL]

variable (O) in
private def sigA : EL Δ τ →ₐ[O] EL Δ τ where
  toFun := sigL
  map_one' := by ext <;> simp [sigL, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' := sg_mul
  map_zero' := by ext <;> simp [sigL]
  map_add' x y := by ext <;> simp [sigL, add_comm]
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply O (Lsq K Δ) (EL Δ τ), IsScalarTower.algebraMap_apply O K (Lsq K Δ)]
    ext <;> simp [sigL]

variable (O Δ) in
private def ofA : Etau K τ →ₐ[O] EL Δ τ where
  toFun := ofE Δ
  map_one' := by ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' x y := by ext <;> simp [ofE]
  map_zero' := by ext <;> simp [ofE]
  map_add' x y := by ext <;> simp [ofE]
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply O (Lsq K Δ) (EL Δ τ), IsScalarTower.algebraMap_apply O K (Lsq K Δ),
      IsScalarTower.algebraMap_apply O K (Etau K τ)]
    ext <;> simp [ofE]

private def cmp (b : Bool) (x : EL Δ τ) : Etau K τ := if b then ⟨x.re.re, x.im.re⟩ else ⟨x.re.im, x.im.im⟩

private theorem semi_semi {c : K} {d m : EL Δ τ} (hd : IsDat c d m) (x : Sp Δ τ) : semi d (semi d x) = (x.1, ω * x.2) := by
  have : ofE Δ (ω : Etau K τ) = ω := by ext <;> simp [ofE]
  simp only [semi, star_star, sg_mul, sg_sg, ← mul_assoc, hd.d_norm, this]

private theorem step1 (h : IsLoc O Δ) {c : K} {d m : EL Δ τ} (hd : IsDat c d m) (x y : ι → Sp Δ τ)
    (h0 : Bd O fun i => herm c m (x i) (y i)) (h1 : Bd O fun i => herm c m (semi d (semi d (x i))) (y i))
    (h2 : Bd O fun i => herm c m (semi d (semi d (semi d (semi d (x i))))) (y i)) :
    (Bd O fun i => (x i).1 * star (y i).1) ∧ Bd O fun i => (x i).2 * star (sigL (y i).2) := by
  haveI := h.frac
  have hτ : 2 - τ ≠ 0 := fun e => hd.reg (by linear_combination (-2 - τ) * e)
  simp only [semi_semi hd] at h1 h2
  have e1 : ∀ (w : EL Δ τ), trace (ω * (ω * w)) = algebraMap K (Lsq K Δ) τ * trace (ω * w) - trace w := fun w => by
    simp only [trace_def, re_mul, im_mul, omega_re, omega_im]; ring
  have hg : Bd O fun i => (x i).1 * star (y i).1 := by
    refine Bd.cancel K (u := algebraMap K (Lsq K Δ) ((2 - τ) * c)) ((mul_ne_zero hτ hd.c_ne).isUnit.map _) ?_
    refine ((h2.add h0).add ((Bd.const K (-algebraMap K (Lsq K Δ) τ)).mul h1)).congr fun i => ?_
    simp only [herm]
    have := e1 (m * (x i).2 * star (sigL (y i).2))
    rw [show m * (ω * (ω * (x i).2)) * star (sigL (y i).2) = ω * (ω * (m * (x i).2 * star (sigL (y i).2))) by ring,
      show m * (ω * (x i).2) * star (sigL (y i).2) = ω * (m * (x i).2 * star (sigL (y i).2)) by ring, this,
      map_mul, map_sub, map_ofNat]
    ring
  refine ⟨hg, ?_⟩
  have hg' := (Bd.const K (-algebraMap K (Lsq K Δ) c)).mul hg
  have t0 : Bd O fun i => trace (m * (x i).2 * star (sigL (y i).2)) :=
    (h0.add hg').congr fun i => by simp only [herm]; ring
  have t1 : Bd O fun i => trace (ω * (m * (x i).2 * star (sigL (y i).2))) :=
    (h1.add hg').congr fun i => by
      simp only [herm]
      rw [show m * (ω * (x i).2) * star (sigL (y i).2) = ω * (m * (x i).2 * star (sigL (y i).2)) by ring]; ring
  let τ' := algebraMap K (Lsq K Δ) τ
  have hu : IsUnit (τ' ^ 2 - 4) := by
    simpa [map_ofNat] using hd.reg.isUnit.map (algebraMap K (Lsq K Δ))
  refine Bd.cancel K hd.m_unit (Bd.cancel K (hu.map (algebraMap (Lsq K Δ) (EL Δ τ))) ?_)
  refine (((t0.map (IsScalarTower.toAlgHom O _ (EL Δ τ))).mul (Bd.const K ⟨τ' ^ 2 - 2, -τ'⟩)).add
    ((t1.map (IsScalarTower.toAlgHom O _ (EL Δ τ))).mul (Bd.const K ⟨-τ', 2⟩))).congr fun i => ?_
  rw [← mul_assoc m]
  generalize m * (x i).2 * star (sigL (y i).2) = w
  simp only [IsScalarTower.toAlgHom_apply]
  refine QuadraticAlgebra.ext ?_ ?_
  · simp only [trace_def, re_mul, im_mul, re_add, omega_re, omega_im, algebraMap_re, algebraMap_im, τ']; ring
  · simp only [trace_def, re_mul, im_mul, im_add, omega_re, omega_im, algebraMap_re, algebraMap_im, τ']; ring

private theorem step2 (h : IsLoc O Δ) {d : EL Δ τ} (hd : IsUnit d) (x y : ι → EL Δ τ)
    (h0 : Bd O fun i => x i * star (sigL (y i))) (h1 : Bd O fun i => x i * star (sigL (d * sigL (y i)))) (b b' : Bool) :
    Bd O fun i => cmp b (x i) * star (cmp b' (y i)) := by
  haveI := h.frac
  have h2 : (2 : K) ≠ 0 := by
    have := (h.two.map (algebraMap O K)).ne_zero
    rwa [map_ofNat] at this
  have hΔ : Δ ≠ 0 := by
    obtain ⟨u, s, hs, hu⟩ := h.even
    rw [hu]; exact mul_ne_zero (u.isUnit.map (algebraMap O K)).ne_zero (pow_ne_zero _ hs)
  have h3 : Bd O fun i => x i * star (y i) :=
    Bd.cancel K (u := star (sigL d)) (hd.map (sigA O)).star (h1.congr fun i => by rw [sg_mul, sg_sg, star_mul]; ring)
  have h4 : Bd O fun i => sigL (x i) * star (y i) :=
    (h0.map (sigA O)).congr fun i => by change _ = sigL _; rw [sg_mul, sg_star, sg_sg]
  have h5 : Bd O fun i => sigL (x i) * star (sigL (y i)) :=
    (h3.map (sigA O)).congr fun i => by change _ = sigL _; rw [sg_mul, sg_star]
  have key : ∀ b, ∃ k : Lsq K Δ, IsUnit k ∧ ∃ e : Lsq K Δ, ∀ w : EL Δ τ,
      algebraMap _ (EL Δ τ) k * ofE Δ (cmp b w) = w + algebraMap _ (EL Δ τ) e * sigL w := by
    intro b
    cases b
    · refine ⟨⟨0, 2⟩, isUnit_iff_norm_isUnit.2 (Ne.isUnit (by simp [QuadraticAlgebra.norm_def, h2, hΔ])), -1, fun w => ?_⟩
      ext <;> simp [cmp, ofE, sigL] <;> ring
    · refine ⟨⟨2, 0⟩, isUnit_iff_norm_isUnit.2 (Ne.isUnit (by simp [QuadraticAlgebra.norm_def, h2])), 1, fun w => ?_⟩
      ext <;> simp [cmp, ofE, sigL] <;> ring
  obtain ⟨k, hk, e, he⟩ := key b
  obtain ⟨k', hk', e', he'⟩ := key b'
  have hs : ∀ a : Lsq K Δ, star (algebraMap _ (EL Δ τ) a) = algebraMap _ (EL Δ τ) a := fun a => by
    refine QuadraticAlgebra.ext ?_ ?_ <;> simp
  have hs' : ∀ a : Etau K τ, ofE Δ (star a) = star (ofE Δ a) := fun a => by ext <;> simp [ofE]
  refine Bd.of_map (ofA O Δ) (fun a b hab => ?_) ?_
  · have : ofE Δ a = ofE Δ b := hab
    simp only [ofE, QuadraticAlgebra.mk.injEq, (algebraMap K (Lsq K Δ)).injective.eq_iff] at this
    exact QuadraticAlgebra.ext this.1 this.2
  refine Bd.cancel K ((hk.map (algebraMap _ (EL Δ τ))).mul (hk'.map (algebraMap _ (EL Δ τ)))) ?_
  refine (((h3.add ((Bd.const K (algebraMap _ (EL Δ τ) e')).mul h0)).add ((Bd.const K (algebraMap _ (EL Δ τ) e)).mul h4)).add
    ((Bd.const K (algebraMap _ (EL Δ τ) e * algebraMap _ (EL Δ τ) e')).mul h5)).congr fun i => ?_
  have e1 := he (x i)
  have e2 := congrArg star (he' (y i))
  rw [star_mul', star_add, star_mul', hs, hs] at e2
  rw [map_mul]
  change _ * (ofE Δ _ * ofE Δ _) = _
  rw [hs', mul_mul_mul_comm, e1, e2]; ring

private theorem step3 (h : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) {e : ι → Etau K τ} (he : Bd O e) :
    (Bd O fun i => (e i).re) ∧ Bd O fun i => (e i).im := by
  haveI := h.frac
  have hinj : Function.Injective (IsScalarTower.toAlgHom O K (Etau K τ)) := algebraMap_injective
  have h1 : Bd O fun i => (e i).im := by
    refine Bd.cancel K hτ.isUnit (Bd.of_map _ hinj ?_)
    refine ((he.add ((Bd.const K (-1)).mul he.star)).mul (Bd.const K ⟨-τ, 2⟩)).congr fun i => ?_
    ext <;> simp [pow_two] <;> ring
  refine ⟨Bd.of_map _ hinj ?_, h1⟩
  refine (he.add ((h1.map (IsScalarTower.toAlgHom O K (Etau K τ))).mul (Bd.const K (-ω)))).congr fun i => ?_
  ext <;> simp

private theorem step4 (h : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) (φ : Sp Δ τ →ₗ[Lsq K Δ] Lsq K Δ) {w : ι → Sp Δ τ}
    (h1 : Bd O fun i => (w i).1) (h2 : ∀ b, Bd O fun i => cmp b (w i).2) : Bd O fun i => φ (w i) := by
  haveI := h.frac
  let j := IsScalarTower.toAlgHom O K (Lsq K Δ)
  have hre : Bd O fun i => (w i).2.re :=
    (((step3 h hτ (h2 true)).1.map j).add (((step3 h hτ (h2 false)).1.map j).mul (Bd.const K ω))).congr fun i => by
      ext <;> simp [j, cmp]
  have him : Bd O fun i => (w i).2.im :=
    (((step3 h hτ (h2 true)).2.map j).add (((step3 h hτ (h2 false)).2.map j).mul (Bd.const K ω))).congr fun i => by
      ext <;> simp [j, cmp]
  refine (((h1.mul (Bd.const K (φ (1, 0)))).add (hre.mul (Bd.const K (φ (0, 1))))).add
    (him.mul (Bd.const K (φ (0, ω))))).congr fun i => ?_
  simp only [← smul_eq_mul, ← map_smul, ← map_add]
  congr 1
  refine Prod.ext (by simp) (QuadraticAlgebra.ext ?_ ?_) <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem core (h : IsLoc O Δ) {c : K} {d m : EL Δ τ} (hd : IsDat c d m) (S : ι → Set (Sp Δ τ))
    (h1 : ∀ y, ∀ x ∈ S y, ∀ x' ∈ S y, IsInt O (herm c m x x')) (h2 : ∀ y, ∀ x ∈ S y, semi d x ∈ S y) :
    (Bd O fun p : (Σ y, S y) => p.2.1.1) ∧
      ∃ N : O, N ≠ 0 ∧ ∀ y, ∀ x ∈ S y, ∀ x' ∈ S y, ∀ b b', IsIntegral O (N • (cmp b x.2 * star (cmp b' x'.2))) := by
  have st : ∀ {κ : Type} (r : κ → ι) (x y : κ → Sp Δ τ), (∀ i, x i ∈ S (r i)) → (∀ i, y i ∈ S (r i)) →
      (Bd O fun i => (x i).1 * star (y i).1) ∧ Bd O fun i => (x i).2 * star (sigL (y i).2) := fun r x y hx hy =>
    step1 h hd x y (Bd.of_int fun i => h1 _ _ (hx i) _ (hy i))
      (Bd.of_int fun i => h1 _ _ (h2 _ _ (h2 _ _ (hx i))) _ (hy i))
      (Bd.of_int fun i => h1 _ _ (h2 _ _ (h2 _ _ (h2 _ _ (h2 _ _ (hx i))))) _ (hy i))
  have hdu : IsUnit d := by
    have : IsUnit (ω : Etau K τ) := isUnit_iff_norm_isUnit.2 (by simp [QuadraticAlgebra.norm_def])
    have h3 : IsUnit (d * sigL d) := hd.d_norm ▸ this.map (ofA O Δ)
    exact isUnit_of_mul_isUnit_left h3
  constructor
  · refine Bd.of_sq ?_
    have := (st (fun p : (Σ y, S y) => p.1) (fun p => p.2.1) (fun p => semi d p.2.1) (fun p => p.2.2)
      (fun p => h2 _ _ p.2.2)).1
    exact this.congr fun p => by simp [semi]
  · have a0 := (st (fun p : (Σ y, S y × S y) => p.1) (fun p => p.2.1.1) (fun p => p.2.2.1) (fun p => p.2.1.2)
      (fun p => p.2.2.2)).2
    have a1 := (st (fun p : (Σ y, S y × S y) => p.1) (fun p => p.2.1.1) (fun p => semi d p.2.2.1) (fun p => p.2.1.2)
      (fun p => h2 _ _ p.2.2.2)).2
    obtain ⟨N, hN, hb⟩ := Bd.fin (κ := Bool × Bool) fun k => step2 h hdu _ _ a0 a1 k.1 k.2
    exact ⟨N, hN, fun y x hx x' hx' b b' => hb ((b, b'), ⟨y, ⟨x, hx⟩, ⟨x', hx'⟩⟩)⟩

private theorem cmp_ofE (b : Bool) (q : Etau K τ) (x : EL Δ τ) : cmp b (ofE Δ q * x) = q * cmp b x := by
  cases b <;> ext <;> simp [cmp, ofE]

end UpperTheory.V.Z.Sym.Loc.FU

open UpperTheory.V.Z.Sym.Loc.FU in
theorem UpperTheory.V.Z.Sym.Loc.finU :
    UpperTheory.V.Z.Sym.Loc.FinU := by
  intro O K _ _ _ _ _ Δ τ h c d m hd δ ι P hP
  let Y := {y : U3 Δ // y⁻¹ * δ * theta Δ y ∈ KU O Δ}
  let S : Y → Set (Sp Δ τ) := fun y => {x | ∃ u : Fin 3 → Lsq K Δ, (∀ i, IsInt O (u i)) ∧
    P x = (y.1 : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ u}
  have h1 : ∀ y, ∀ x ∈ S y, ∀ x' ∈ S y, IsInt O (herm c m x x') := by
    rintro y x ⟨u, hu, hx⟩ x' ⟨v, hv, hx'⟩
    have e : herm c m x x' = ∑ i, u i * star (v i) := by
      rw [hP.form, hx, hx']
      change _ ⬝ᵥ star _ = u ⬝ᵥ star v
      rw [star_mulVec, dotProduct_comm, dotProduct_mulVec, vecMul_vecMul, ← Matrix.star_eq_conjTranspose, y.1.2.1,
        vecMul_one, dotProduct_comm]
    rw [e]
    exact IsIntegral.sum _ fun i _ => (hu i).mul (isIntegral_star_quad (hv i))
  have h2 : ∀ y, ∀ x ∈ S y, semi d x ∈ S y := by
    rintro y x ⟨u, hu, hx⟩
    refine ⟨((y.1⁻¹ * δ * theta Δ y.1 : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star u, fun i => ?_, ?_⟩
    · exact IsIntegral.sum (s := Finset.univ) _ fun j _ => (y.2 i j).1.mul (isIntegral_star_quad (hu j))
    · rw [hP.semi, hx, mulVec_mulVec, ← Submonoid.coe_mul, mul_assoc, mul_inv_cancel_left, Submonoid.coe_mul,
        ← mulVec_mulVec]
      congr 1
      funext i
      simp [theta, mulVec, dotProduct, star_sum]
  obtain ⟨b1, N, hN, b2⟩ := core h hd S h1 h2
  let col : Y → Fin 3 → Sp Δ τ := fun y j => P.symm ((y.1 : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ Pi.single j 1)
  have hcol : ∀ y j, col y j ∈ S y := fun y j => ⟨Pi.single j 1, fun i => by
    by_cases hij : i = j <;> simp [Pi.single_apply, hij, isIntegral_one, isIntegral_zero], P.apply_symm_apply _⟩
  choose z hz using fun y : Y => tor_bound h hd.reg N (fun p : Bool × Fin 3 => cmp p.1 (col y p.2).2)
    fun p q => b2 y _ (hcol y p.2) _ (hcol y q.2) p.1 q.1
  obtain ⟨M, hM, hb⟩ := Bd.fin (κ := Fin 3) fun i =>
    step4 h hd.reg ((LinearMap.proj i).comp P.toLinearMap) (w := fun p : Y × Fin 3 => tor Δ (z p.1) (col p.1 p.2))
      (b1.comp fun p : Y × Fin 3 => ⟨p.1, _, hcol p.1 p.2⟩)
      fun b => ⟨N, hN, fun p => by simpa only [tor, cmp_ofE] using hz p.1 (b, p.2)⟩
  obtain ⟨s, hs⟩ := fin_cosets h hM
  refine ⟨s, fun y hy => ?_⟩
  obtain ⟨x, hx, k, hk, e⟩ := hs (ι (z ⟨y, hy⟩) * y) fun i j => by
    have := hb (i, ⟨y, hy⟩, j)
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe, hP.tor, col, P.apply_symm_apply,
      mulVec_mulVec, mulVec_single_one] at this
    exact this
  exact ⟨(z ⟨y, hy⟩)⁻¹, x, hx, k, hk, by rw [map_inv, mul_assoc, ← e, inv_mul_cancel_left]⟩
