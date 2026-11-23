import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductDistributionRelationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplexStatement

open scoped MatrixGroups Matrix UpperHalfPlane
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

namespace UpperTheory.V.Z.Kato.Sym.SiegelIsogeny

open GlobalTheory.Sieg

private theorem prod_cth (c m : ℕ) (q t : ℂ) (hm : 0 < m) (hc : Nat.Coprime c m) (hq : ‖q‖ < 1) (ht : t ≠ 0) :
    ∏ j ∈ Finset.range m, cth c q (t * ee ((j : ℂ) / m)) = cth c (q ^ m) (t ^ m) := by
  have hm0 : m ≠ 0 := hm.ne'
  have hζ : IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / m)) m :=
    Complex.isPrimitiveRoot_exp m hm0
  set ζ := Complex.exp (2 * ↑Real.pi * Complex.I / m) with hζd
  have he : ∀ j : ℕ, ee ((j : ℂ) / m) = ζ ^ j := fun j => ee_nat_div_eq_pow m j
  simp_rw [he]
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hm0
  have hne : ∀ j : ℕ, t * ζ ^ j ≠ 0 := fun j => mul_ne_zero ht (pow_ne_zero _ hζ0)
  have p1 : ∏ j ∈ Finset.range m, (-(t * ζ ^ j)) = -(t ^ m) := by
    have h := prod_sub_pow_mul_of_isPrimitiveRoot hζ hm 0 t
    rw [zero_pow hm0, zero_sub] at h
    rw [← h]
    refine Finset.prod_congr rfl fun j _ => ?_
    ring
  have p2 : ∏ j ∈ Finset.range m, (1 - t * ζ ^ j) = 1 - t ^ m := by
    have h := prod_sub_pow_mul_of_isPrimitiveRoot hζ hm 1 t
    rw [one_pow] at h
    rw [← h]
    refine Finset.prod_congr rfl fun j _ => ?_
    ring
  have p3 : ∏ j ∈ Finset.range m, (1 - (t * ζ ^ j) ^ c) = 1 - (t ^ m) ^ c := by
    have h := prod_sub_pow_mul_of_isPrimitiveRoot (hζ.pow_of_coprime c hc) hm 1 (t ^ c)
    rw [one_pow] at h
    rw [← pow_mul, mul_comm m c, pow_mul, ← h]
    refine Finset.prod_congr rfl fun j _ => ?_
    ring
  have p4 : ∏ j ∈ Finset.range m, ∏' n : ℕ, cthFac c q (t * ζ ^ j) (n + 1) =
      ∏' n : ℕ, cthFac c (q ^ m) (t ^ m) (n + 1) := by
    rw [← Multipliable.tprod_finsetProd (fun j _ => cthFac_multipliable c q _ hq (hne j))]
    refine tprod_congr fun n => ?_
    exact prod_cthFac_mul_pow hζ hm hc q t (n + 1)
  simp only [cth, Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_pow, Finset.prod_zpow,
    Finset.prod_const, Finset.card_range, p1, p2, p3, p4]

private theorem prod_sg (c k : ℕ) (x : Fin 2 → ℚ) (τ τ' : ℍ) (hk : 0 < k) (hc : Nat.Coprime c k)
    (h : (τ' : ℂ) = k * τ) :
    ∏ j ∈ Finset.range k, GlobalTheory.Sieg.sg c ![x 0, (x 1 + j) / k] τ = GlobalTheory.Sieg.sg c x τ' := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hq : ‖ee (τ : ℂ)‖ < 1 := by
    rw [ee, Complex.norm_exp, Real.exp_lt_one_iff]
    have hre : (2 * ↑Real.pi * Complex.I * (τ : ℂ)).re = -(2 * Real.pi * τ.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have := τ.im_pos
    nlinarith [Real.pi_pos]
  set T := ee ((x 0 : ℂ) * τ + (x 1 : ℂ) / k) with hT
  have hT0 : T ≠ 0 := Complex.exp_ne_zero _
  have key := prod_cth c k (ee τ) T hk hc hq hT0
  have h1 : ∀ j ∈ Finset.range k, GlobalTheory.Sieg.sg c ![x 0, (x 1 + j) / k] τ = cth c (ee τ) (T * ee ((j : ℂ) / k)) := by
    intro j _
    simp only [GlobalTheory.Sieg.sg, pt, hT, ee, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  rw [Finset.prod_congr rfl h1, key, GlobalTheory.Sieg.sg]
  congr 1
  · simp only [ee, ← Complex.exp_nat_mul, h]
    congr 1
    ring
  · simp only [hT, pt, ee, ← Complex.exp_nat_mul, h]
    congr 1
    field_simp

private theorem siegel_admissible_to_rat (c M : ℕ) [NeZero M] (h1 : 1 < c) (h6 : Nat.Coprime c 6) (hc : Nat.Coprime c M) (x : Row M)
    (hx : x ≠ 0) : GlobalTheory.Sieg.admitted c (toQ M x) := by
  refine ⟨h1, h6, ?_⟩
  rintro ⟨⟨n0, hn0⟩, ⟨n1, hn1⟩⟩
  have hM : (M : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have key : ∀ i, ∀ n : ℤ, (n : ℚ) = c * toQ M x i → x i = 0 := by
    intro i n hn
    simp only [toQ] at hn
    have h2 : n * (M : ℤ) = ((c * (x i).val : ℕ) : ℤ) := by
      have h3 : (n : ℚ) * M = c * (x i).val := by rw [hn]; field_simp
      exact_mod_cast h3
    have hdvd : (M : ℤ) ∣ ((c * (x i).val : ℕ) : ℤ) := ⟨n, by rw [← h2]; ring⟩
    have hdvd' : M ∣ c * (x i).val := Int.natCast_dvd_natCast.mp hdvd
    have hv : M ∣ (x i).val := Nat.Coprime.dvd_of_dvd_mul_left hc.symm hdvd'
    have hlt : (x i).val < M := ZMod.val_lt _
    have h0 : (x i).val = 0 := Nat.eq_zero_of_dvd_of_lt hv hlt
    exact (ZMod.val_eq_zero _).mp h0
  apply hx
  funext i
  fin_cases i
  · exact key 0 n0 hn0
  · exact key 1 n1 hn1

private theorem neBot : (Filter.codiscreteWithin Hs).NeBot := by
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have hopen : IsOpen Hs := by
    show IsOpen {z : ℂ | 0 < z.im}
    exact isOpen_lt continuous_const Complex.continuous_im
  have hnb : (nhdsWithin Complex.I (Hs \ {Complex.I})).NeBot := by
    rw [Set.diff_eq, nhdsWithin_inter_of_mem
      (mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hI))]
    infer_instance
  refine hnb.mono ?_
  exact le_iSup₂ (f := fun x (_ : x ∈ Hs) => nhdsWithin x (Hs \ {x})) Complex.I hI

private theorem mob_dg (k : ℕ) (hk : 0 < k) (z : ℂ) : mob (dg k) z = k * z := by
  simp [mob, dg, toGQ, ent, Matrix.det_fin_two, hk, Matrix.GeneralLinearGroup.mk']

private theorem prod_siegel {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (c k : ℕ) (x : Fin 2 → ℚ) (hA : GlobalTheory.Sieg.admitted c x) (hk : 0 < k) (hc : Nat.Coprime c k) :
    ∏ j ∈ Finset.range k, siegel X c ![x 0, (x 1 + j) / k] = X.sl (dg k) (siegel X c x) := by
  haveI := neBot
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hAj : ∀ j ∈ Finset.range k, GlobalTheory.Sieg.admitted c ![x 0, (x 1 + j) / k] := by
    intro j _
    obtain ⟨h1, h6, hn⟩ := hA
    refine ⟨h1, h6, ?_⟩
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    apply hn
    have ha' : (a : ℚ) = c * x 0 := by simpa using ha
    have hb' : (b : ℚ) = c * ((x 1 + j) / k) := by simpa using hb
    refine ⟨⟨a, ha'⟩, ⟨b * k - c * j, ?_⟩⟩
    push_cast
    rw [hb']
    field_simp
    ring
  apply X.an.injective
  rw [map_prod, Finset.prod_congr rfl (fun j hj => GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε X c _ (hAj j hj)),
    X.an_sl (dg k) _ (sgC c x) (GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε X c x hA)]
  have hprod : ∏ j ∈ Finset.range k, (↑(sgC c ![x 0, (x 1 + j) / k]) : Mero) =
      ↑(∏ j ∈ Finset.range k, sgC c ![x 0, (x 1 + j) / k]) :=
    (map_prod (Filter.Germ.coeRingHom _) _ _).symm
  rw [hprod, Filter.Germ.coe_eq]
  filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
  have hz' : 0 < z.im := hz
  have hkz : 0 < ((k : ℂ) * z).im := by
    simpa [Complex.mul_im] using mul_pos (Nat.cast_pos.mpr hk : (0 : ℝ) < k) hz'
  simp only [Finset.prod_apply]
  show _ = sgC c x (mob (dg k) z)
  rw [mob_dg k hk]
  simp only [sgC, UpperHalfPlane.ofComplex_apply_of_im_pos hz', UpperHalfPlane.ofComplex_apply_of_im_pos hkz]
  exact prod_sg c k x ⟨z, hz'⟩ ⟨k * z, hkz⟩ hk hc rfl

end UpperTheory.V.Z.Kato.Sym.SiegelIsogeny

open UpperTheory.V.Z.Kato.Sym.SiegelIsogeny in
theorem UpperTheory.V.Z.Kato.Sym.sgIsog :
    UpperTheory.V.Z.Kato.Sym.SgIsog := by
  intro Ω _ _ _ ε X c k M _ h1 h6 hc x hx
  have hkM : k * M ≠ 0 := NeZero.ne _
  have hk : 0 < k := Nat.pos_of_ne_zero (left_ne_zero_of_mul hkM)
  have hM : 0 < M := Nat.pos_of_ne_zero (right_ne_zero_of_mul hkM)
  haveI : NeZero M := ⟨hM.ne'⟩
  have hck : c.Coprime k := Nat.Coprime.coprime_dvd_right (dvd_mul_right k M) hc
  have hcM : c.Coprime M := Nat.Coprime.coprime_dvd_right (dvd_mul_left M k) hc
  have hx0 : (x 0).val < M := ZMod.val_lt _
  have hx1 : (x 1).val < M := ZMod.val_lt _
  have hlt0 : k * (x 0).val < k * M := by nlinarith
  have hlt1 : ∀ j, j < k → (x 1).val + j * M < k * M := by
    intro j hj
    nlinarith [Nat.zero_le M]
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [UpperTheory.V.Z.Kato.Sym.sg]
  rw [← prod_siegel X c k (toQ M x) (siegel_admissible_to_rat c M h1 h6 hcM x hx) hk hck]
  symm
  refine Finset.prod_nbij'
    (i := fun j => ![((k * (x 0).val : ℕ) : ZMod (k * M)), (((x 1).val + j * M : ℕ) : ZMod (k * M))])
    (j := fun x' => (x' 1).val / M) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨rfl, ?_⟩
    show ZMod.castHom _ (ZMod M) (((x 1).val + j * M : ℕ) : ZMod (k * M)) = x 1
    rw [map_natCast, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero,
      ZMod.natCast_zmod_val]
  · intro x' hx'
    rw [Finset.mem_range]
    have hv : (x' 1).val < k * M := ZMod.val_lt _
    exact (Nat.div_lt_iff_lt_mul hM).mpr hv
  · intro j hj
    have hj' : j < k := Finset.mem_range.mp hj
    show (((x 1).val + j * M : ℕ) : ZMod (k * M)).val / M = j
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hlt1 j hj'), Nat.add_mul_div_right _ _ hM,
      Nat.div_eq_of_lt hx1, zero_add]
  · intro x' hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx'
    obtain ⟨h0, h1'⟩ := hx'
    have h2 : ((x' 1).val : ZMod M) = x 1 := by
      rw [← h1']
      show _ = ZMod.castHom _ (ZMod M) (x' 1)
      rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    have hmod : (x' 1).val % M = (x 1).val := by
      have h3 := congrArg ZMod.val h2
      rwa [ZMod.val_natCast] at h3
    funext i
    fin_cases i
    · exact h0.symm
    · show (((x 1).val + (x' 1).val / M * M : ℕ) : ZMod (k * M)) = x' 1
      rw [← hmod, Nat.mod_add_div', ZMod.natCast_zmod_val]
  · intro j hj
    have hj' : j < k := Finset.mem_range.mp hj
    congr 1
    funext i
    fin_cases i
    · show ((x 0).val : ℚ) / M =
        ((((k * (x 0).val : ℕ) : ZMod (k * M)).val : ℕ) : ℚ) / ((k * M : ℕ) : ℚ)
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt0]
      push_cast
      field_simp <;> ring
    · show (((x 1).val : ℚ) / M + j) / k =
        (((((x 1).val + j * M : ℕ) : ZMod (k * M)).val : ℕ) : ℚ) / ((k * M : ℕ) : ℚ)
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hlt1 j hj')]
      push_cast
      field_simp <;> ring
