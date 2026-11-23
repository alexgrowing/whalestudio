import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.Unitarize

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V.Af
open scoped Matrix NNReal

namespace UpperTheory.V.Sd.Wc

section

variable {F : Type} [Field F] [NumberField F]

private theorem congruence_subgroup_one_entry_bounds (w : Pl F) {g : GL (Fin 2) (w.adicCompletion F)} (hg : g ∈ K1 w 1) :
    (∀ i j, Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j) ≤ 1) ∧
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 0) < 1 ∧
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 1 - 1) < 1 ∧
      Valued.v (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)).det = 1 := by
  obtain ⟨k, hk, rfl⟩ := hg
  have hk' := hk
  change ![0, 1] ᵥ* _ = ![0, 1] at hk'
  have hm : ∀ x : w.adicCompletionIntegers F, x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 1 →
      Valued.v (x : w.adicCompletion F) < 1 := by
    intro x hx
    rw [pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hx
    exact lt_of_le_of_ne x.2 hx
  have h0 := congrFun hk' 0
  have h1 := congrFun hk' 1
  refine ⟨fun i j => (k i j).2, hm (k 1 0) ?_, hm (k 1 1 - 1) ?_, ?_⟩
  · simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Ideal.Quotient.eq_zero_iff_mem] using h0
  · refine Ideal.Quotient.eq.1 ?_
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ] using h1
  · have hu : IsUnit (k : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers F)).det :=
      (Matrix.GeneralLinearGroup.det k).isUnit
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hu
    rw [← hu]
    exact congrArg Valued.v ((w.adicCompletionIntegers F).subtype.map_det _).symm

private def low {R : Type} [CommRing R] (x : R) : GL (Fin 2) R where
  val := !![1, 0; x, 1]
  inv := !![1, 0; -x, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

private theorem low_mem (w : Pl F) (x : w.adicCompletion F) (hx : Valued.v x < 1) : low x ∈ K1 w 1 := by
  let y : w.adicCompletionIntegers F := ⟨x, hx.le⟩
  have hy : y ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 1 := by
    rw [pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hx.ne
  refine ⟨low y, ?_, ?_⟩
  · change ![0, 1] ᵥ* _ = ![0, 1]
    ext j
    fin_cases j
    · simpa [low, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Ideal.Quotient.eq_zero_iff_mem] using hy
    · simp [low, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [low, y]

private theorem loc_mem_Kc (c : Pl F → ℕ) (w : Pl F) {k : GL (Fin 2) (w.adicCompletion F)} (hk : k ∈ K1 w (c w)) :
    locGL F 2 w k ∈ Kc c := by
  refine Subgroup.mem_iInf.2 fun u => Subgroup.mem_comap.2 ?_
  by_cases h : u = w
  · subst h; rwa [pLoc_locGL]
  · rw [pLoc_locGL_of_ne h]; exact one_mem _

variable {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} (D : LDat F ι)

private theorem gl_apply (k : GF F) (v : InfinitePlace F) :
    D.gl k v = Matrix.GeneralLinearGroup.map (D.em v) (Matrix.GeneralLinearGroup.map (pLoc F (D.pl v)) k) := by
  ext i j; rfl

private theorem nu_eq_one (v : InfinitePlace F) {x : (D.pl v).adicCompletion F} (hx : Valued.v x = 1) : nu ι (D.em v x) = 1 :=
  le_antisymm ((D.le v x).2 hx.le) (not_lt.1 fun h => ((D.lt v x).1 h).ne hx)

open Classical in
private theorem gl_loc (v : InfinitePlace F) (a : GL (Fin 2) ((D.pl v).adicCompletion F)) :
    D.gl (locGL F 2 (D.pl v) a) = Pi.mulSingle v (Matrix.GeneralLinearGroup.map (D.em v) a) := by
  funext u
  rw [gl_apply]
  by_cases h : u = v
  · subst h; rw [pLoc_locGL, Pi.mulSingle_eq_same]
  · rw [pLoc_locGL_of_ne (fun e => h (D.inj e)), Pi.mulSingle_eq_of_ne h, map_one]

private theorem unit_val (v : InfinitePlace F) : ∃ x : (D.pl v).adicCompletion F, Valued.v x = 1 ∧
    D.em v x = v.embedding (unif (D.pl v) : Fˣ) / (l : ℂ) := by
  have hp : Valued.v ((atFin (D.pl v) (unif (D.pl v)) : ((D.pl v).adicCompletion F)ˣ) : (D.pl v).adicCompletion F) =
    WithZero.exp (-1 : ℤ) := unif_spec _
  refine ⟨((atFin (D.pl v) (unif (D.pl v)) : ((D.pl v).adicCompletion F)ˣ) : (D.pl v).adicCompletion F) / (l : _), ?_, ?_⟩
  · rw [map_div₀, hp, D.unif, div_self WithZero.exp_ne_zero]
  · rw [map_div₀, map_natCast, ← D.em_alg]; rfl

end

private theorem val_mul_sub {ν : Valuation ℂ ℝ≥0} {x y : ℂ} (hx : ν (x - 1) < 1) (hy : ν (y - 1) < 1) : ν (x * y - 1) < 1 := by
  have e : x * y - 1 = (x - 1) * (y - 1) + ((x - 1) + (y - 1)) := by ring
  rw [e]
  refine ν.map_add_lt ?_ (ν.map_add_lt hx hy)
  rw [map_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hx hy.le

private theorem val_zpow_sub {ν : Valuation ℂ ℝ≥0} {x : ℂ} (h1 : ν x = 1) (hx : ν (x - 1) < 1) (m : ℤ) : ν (x ^ m - 1) < 1 := by
  have hn : ∀ y : ℂ, ν (y - 1) < 1 → ∀ n : ℕ, ν (y ^ n - 1) < 1 := by
    intro y hy n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ]; exact val_mul_sub ih hy
  have h0 : x ≠ 0 := by rintro rfl; simp at h1
  obtain ⟨n, rfl | rfl⟩ := m.eq_nat_or_neg
  · rw [zpow_natCast]; exact hn x hx n
  · rw [zpow_neg, zpow_natCast, ← inv_pow]
    refine hn _ ?_ n
    have e : x⁻¹ - 1 = -(x⁻¹ * (x - 1)) := by field_simp; ring
    rwa [e, Valuation.map_neg, map_mul, map_inv₀, h1, inv_one, one_mul]

end UpperTheory.V.Sd.Wc

open UpperTheory.V.Sd.Wc in
theorem UpperTheory.V.Sd.Wc.glFacts :
    UpperTheory.V.Sd.Wc.GlFacts := by
  classical
  intro F _ _ l _ ι D
  have huf : ∀ e w, nu ι (D.uf e w) = 1 := by
    intro e w
    rw [LDat.uf, map_prod]
    refine Finset.prod_eq_one fun v _ => ?_
    split_ifs with h
    · subst h
      obtain ⟨x, hx, e⟩ := unit_val D v
      rw [← e, map_zpow₀, nu_eq_one D v hx, one_zpow]
    · exact map_one _
  refine ⟨fun c hc => ⟨fun k hk v => ?_, fun a => ?_⟩, fun w hw a => ?_, gl_loc D, fun n e z x => ?_, huf, fun e e' he w => ?_⟩
  · have h1 := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hk (D.pl v))
    rw [hc] at h1
    obtain ⟨ha, hb, hd, he⟩ := congruence_subgroup_one_entry_bounds _ h1
    have hdet : (D.gl k v : Matrix (Fin 2) (Fin 2) ℂ).det = D.em v
        (Matrix.GeneralLinearGroup.map (pLoc F (D.pl v)) k : Matrix (Fin 2) (Fin 2) ((D.pl v).adicCompletion F)).det :=
      ((D.em v).map_det _).symm
    refine ⟨fun i j => (D.le v _).2 (ha i j), (D.lt v _).2 hb, ?_, ?_, ?_⟩
    · have := (D.lt v _).2 hd
      rwa [map_sub, map_one] at this
    · rw [hdet]; exact nu_eq_one D v he
    · rw [hdet]; exact D.res v _ he
  · have key : ∀ s : Finset (InfinitePlace F), ∃ k ∈ Kc c, ∀ v,
        D.gl k v = if v ∈ s then low ((l * a v : ℕ) : ℂ) else 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨1, one_mem _, fun v => by simp⟩
      | insert u s hu ih =>
        obtain ⟨k, hk, hv⟩ := ih
        have hl : Valued.v ((l * a u : ℕ) : (D.pl u).adicCompletion F) < 1 := by
          rw [Nat.cast_mul, map_mul, D.unif]
          have h2 : Valued.v ((a u : ℕ) : (D.pl u).adicCompletion F) ≤ 1 :=
            natCast_mem ((D.pl u).adicCompletionIntegers F) (a u)
          refine mul_lt_one_of_nonneg_of_lt_one_left zero_le ?_ h2
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
        refine ⟨locGL F 2 (D.pl u) (low ((l * a u : ℕ) : (D.pl u).adicCompletion F)) * k,
          mul_mem (loc_mem_Kc c _ (by rw [hc]; exact low_mem _ _ hl)) hk, fun v => ?_⟩
        rw [map_mul, Pi.mul_apply, gl_loc, hv]
        by_cases h : v = u
        · subst h
          rw [Pi.mulSingle_eq_same, if_neg hu, mul_one, if_pos (Finset.mem_insert_self _ _)]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [low]
        · rw [Pi.mulSingle_eq_of_ne h, one_mul]
          simp [h]
    obtain ⟨k, hk, hv⟩ := key Finset.univ
    exact ⟨k, hk, fun v => by rw [hv, if_pos (Finset.mem_univ _)]; rfl⟩
  · funext v
    rw [gl_apply, pLoc_locGL_of_ne (fun e : D.pl v = w => hw (e ▸ D.mem v)), map_one, Pi.one_apply]
  · refine Subtype.ext (MvPolynomial.funext fun y => ?_)
    have hg : ∀ v, (D.gl (zc F z) v : Matrix (Fin 2) (Fin 2) ℂ) = !![D.ea v z, 0; 0, D.ea v z] := by
      intro v
      ext i j
      change D.ea v ((zc F z : Matrix (Fin 2) (Fin 2) (Af F)) i j) = _
      fin_cases i <;> fin_cases j <;> simp [zc]
    have h0 : ∀ v, D.ea v z ≠ 0 := fun v => (z.isUnit.map (D.ea v)).ne_zero
    have ha : act (D.gl (zc F z)) y = fun p => D.ea p.1 z * y p := by
      funext p
      obtain ⟨v, i⟩ := p
      fin_cases i <;> simp [act, hg, mul_comm]
    have hd : (detE e (D.gl (zc F z)) : ℂ) = ∏ v, D.ea v z ^ (2 * e v) := by
      change ((∏ v, Matrix.GeneralLinearGroup.det (D.gl (zc F z) v) ^ e v : ℂˣ) : ℂ) = _
      rw [Units.coe_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, hg, zpow_mul, zpow_two]
      simp
    change MvPolynomial.eval y (wRep n e (D.gl (zc F z)) x).1 = MvPolynomial.eval y (_ • x.1)
    rw [eval_wRep, ha, x.2 (fun v => D.ea v z) y, MvPolynomial.smul_eval, hd, ← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [zpow_add₀ (h0 v), zpow_natCast, mul_comm]
  · by_cases hw : ∃ v, D.pl v = w
    · obtain ⟨v, rfl⟩ := hw
      obtain ⟨x, hx, ex⟩ := unit_val D v
      have hs : ∀ e, D.uf e (D.pl v) = D.em v x ^ e v := by
        intro e
        rw [LDat.uf, Finset.prod_eq_single v (fun u _ hu => if_neg fun h => hu (D.inj h)) (by simp), if_pos rfl, ex]
      have h1 := nu_eq_one D v hx
      have h0 : D.em v x ≠ 0 := by intro h; rw [h] at h1; simp at h1
      obtain ⟨m, hm⟩ := he v
      have hl : ((l - 1 : ℕ) : ℤ) = (l : ℤ) - 1 := by
        rw [Nat.cast_sub (Fact.out : l.Prime).one_le, Nat.cast_one]
      have e1 : D.em v x ^ e' v - D.em v x ^ e v = D.em v x ^ e v * ((D.em v x ^ (l - 1)) ^ m - 1) := by
        rw [← zpow_natCast, ← zpow_mul, hl, ← hm, mul_sub, ← zpow_add₀ h0, mul_one, add_sub_cancel]
      rw [hs, hs, e1, map_mul, map_zpow₀, h1, one_zpow, one_mul]
      exact val_zpow_sub (by rw [map_pow, h1, one_pow]) (D.res v x hx) m
    · have hs : ∀ e, D.uf e w = 1 := fun e => Finset.prod_eq_one fun v _ => if_neg fun h => hw ⟨v, h⟩
      rw [hs, hs, sub_self, map_zero]
      exact zero_lt_one
