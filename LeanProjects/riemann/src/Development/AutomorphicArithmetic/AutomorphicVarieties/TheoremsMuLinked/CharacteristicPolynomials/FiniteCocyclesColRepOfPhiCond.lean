import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.ContinuousCocyclesFgIntegralOfPhiCond
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.CocField
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IntModel
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem zc_norm {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) : ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[l] (x : PadicAlgCl l) := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map c.O.val
  have h0 : ‖(x : PadicAlgCl l)‖ = spectralValue (minpoly ℚ_[l] (x : PadicAlgCl l)) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral _))]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

private theorem zc_dvd {l : ℕ} [Fact l.Prime] (c : Coef l) (x y : c.O)
    (h : ‖(x : PadicAlgCl l)‖ < ‖(y : PadicAlgCl l)‖) : y ∣ x := by
  rcases ValuationRing.dvd_total y x with h1 | ⟨u, rfl⟩
  · exact h1
  · exfalso
    rw [Subalgebra.coe_mul, norm_mul] at h
    exact absurd (mul_le_of_le_one_right (norm_nonneg _) (zc_norm c u)) (not_le.2 h)

private theorem zc_ev {l : ℕ} [hl : Fact l.Prime] {G : Type} [TopologicalSpace G] (c : Coef l)
    (f : G → c.O) (hf : Continuous fun g => (f g : PadicAlgCl l)) (N : ℕ) (x : G) :
    ∀ᶠ y in nhds x, (l : c.O) ^ N ∣ f y - f x := by
  have hl0 : (l : PadicAlgCl l) ^ N ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)
  have h1 : ∀ᶠ y in nhds x, ‖(f y : PadicAlgCl l) - f x‖ < ‖(l : PadicAlgCl l) ^ N‖ :=
    ((hf.sub continuous_const).norm.tendsto x).eventually_lt_const (by simpa using norm_pos_iff.2 hl0)
  filter_upwards [h1] with y hy
  exact zc_dvd c _ _ (by push_cast; exact hy)

private theorem zc_split {l : ℕ} [hl : Fact l.Prime] (c c' : Coef l) (hcc : c.O ≤ c'.O) {G : Type} [Group G]
    [TopologicalSpace G] {m : ℕ} (σ : G →* GL (Fin m) c.O) (z : G → Fin m → PadicAlgCl l) (hz : Continuous z)
    (hm : ∀ g i, z g i ∈ c'.O)
    (hc : ∀ g h, z (g * h) = z g + W.mat (W.pushRep (algebraMap c.O (PadicAlgCl l)) σ) g *ᵥ z h) :
    ∃ (n : ℕ) (b : Fin n → PadicAlgCl l) (w : Fin n → G → Fin m → c.O),
      (∀ k, (∀ i, AdicCont (maximalIdeal c.O) fun g => w k g i) ∧
        ∀ g h, w k (g * h) = w k g + W.mat σ g *ᵥ w k h) ∧
      ∀ g i, z g i = ∑ k, b k * (w k g i : PadicAlgCl l) := by
  obtain ⟨-, -, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  letI : Algebra c.O c'.O := (Subalgebra.inclusion hcc).toRingHom.toAlgebra
  have ha : ∀ (a : c.O) (x : c'.O), ((a • x : c'.O) : PadicAlgCl l) = a * x := fun _ _ => rfl
  haveI : IsScalarTower ℤ_[l] c.O c'.O := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite c.O c'.O := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  haveI : FaithfulSMul c.O c'.O := (faithfulSMul_iff_algebraMap_injective _ _).2 (Subalgebra.inclusion_injective hcc)
  haveI : Module.Free c.O c'.O := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis c.O c'.O
  let f : G → Fin m → c'.O := fun g i => ⟨z g i, hm g i⟩
  refine ⟨_, fun k => b k, fun k g i => b.coord k (f g i), fun k => ⟨fun i N => ?_, fun g h => ?_⟩, fun g i => ?_⟩
  · refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    filter_upwards [zc_ev c' (fun g => f g i) ((continuous_apply i).comp hz) N x] with y ⟨u, hu⟩
    have e : (l : c'.O) ^ N * u = ((l : c.O) ^ N) • u := by rw [Algebra.smul_def, map_pow, map_natCast]
    rw [Ideal.Quotient.eq, ← map_sub, hu, e, map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlm N)
  · funext i
    have e : f (g * h) i = f g i + ∑ j, W.mat σ g i j • f h j := Subtype.ext (by
      rw [Subalgebra.coe_add, AddSubmonoidClass.coe_finset_sum]
      exact congrFun (hc g h) i)
    simp only [e, map_add, map_sum, map_smul, Pi.add_apply, Matrix.mulVec, dotProduct, smul_eq_mul]
  · have e := congrArg Subtype.val (b.sum_repr (f g i))
    rw [AddSubmonoidClass.coe_finset_sum] at e
    refine e.symm.trans (Finset.sum_congr rfl fun k _ => ?_)
    rw [ha, mul_comm]
    rfl

theorem UpperTheory.V.Th.Det.finite_cocycles_colRep_of_phiCond :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {m : ℕ} (σ : G →* GL (Fin m) (Qbar l)), PhiCond G l → Continuous σ → Module.Finite (Qbar l) (Z1 (Loc.colRep σ)) := by
  intro l _ G _ _ _ _ _ m σ hΦ hσ
  classical
  obtain ⟨c₀, -⟩ := UpperTheory.V.X.So.coefOf l ⊥
  obtain ⟨c, Q, σ₀, -, hQ, hσ₀⟩ := UpperTheory.V.Ws.Eb.intModel c₀ σ hσ
  have hQ' : ∀ g, W.pushRep (algebraMap c.O (PadicAlgCl l)) σ₀ g = Q⁻¹ * σ g * Q := fun g => by
    rw [mul_assoc, hQ, inv_mul_cancel_left]
  let Z : Submodule c.O (G → Fin m → c.O) :=
    { carrier := {z | (∀ i, AdicCont (maximalIdeal c.O) fun g => z g i) ∧
          ∀ g h, z (g * h) = z g + W.mat σ₀ g *ᵥ z h}
      add_mem' := fun {a b} ha hb => ⟨fun i N => by
          simp only [Pi.add_apply, map_add]; exact (ha.1 i N).add (hb.1 i N),
        fun g h => by simp only [Pi.add_apply, Matrix.mulVec_add, ha.2 g h, hb.2 g h]; abel⟩
      zero_mem' := ⟨fun i N => by
          simp only [Pi.zero_apply, map_zero]; exact IsLocallyConstant.const _, fun g h => by simp⟩
      smul_mem' := fun r a ha => ⟨fun i N => by
          simp only [Pi.smul_apply, smul_eq_mul, map_mul]
          exact (ha.1 i N).comp (fun x => Ideal.Quotient.mk _ r * x),
        fun g h => by simp only [Pi.smul_apply, Matrix.mulVec_smul, ha.2 g h, smul_add]⟩ }
  obtain ⟨s, hs⟩ := UpperTheory.V.Th.Det.continuousCocycles_fg_integral_of_phiCond c σ₀ Z hΦ hσ₀ fun z hz => hz
  let ι : (G → Fin m → c.O) → G → Fin m → PadicAlgCl l := fun w g i => (w g i : PadicAlgCl l)
  let S : Submodule (PadicAlgCl l) (G → Fin m → PadicAlgCl l) := Submodule.span _ (ι '' s)
  have hS : ∀ w ∈ Z, ι w ∈ S := by
    intro w hw
    rw [← hs] at hw
    induction hw using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => exact S.zero_mem
    | add y z _ _ hy hz => exact S.add_mem hy hz
    | smul a y _ hy => exact S.smul_mem (a : PadicAlgCl l) hy
  let T : (G → Fin m → PadicAlgCl l) →ₗ[PadicAlgCl l] (G → Fin m → PadicAlgCl l) :=
    (Matrix.toLin' (Q : Matrix (Fin m) (Fin m) (PadicAlgCl l))).compLeft G
  have hfg : (S.map T).FG := (Submodule.fg_span (s.finite_toSet.image ι)).map T
  refine Module.Finite.iff_fg.2 (Submodule.FG.of_le hfg fun z hz => ?_)
  let z' : G → Fin m → PadicAlgCl l := fun g => ((Q⁻¹ : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) *ᵥ z g
  have hT : ∀ g, (Q : Matrix (Fin m) (Fin m) (PadicAlgCl l)) *ᵥ z' g = z g := fun g => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hz' : Continuous z' := continuous_const.matrix_mulVec hz.1
  have hc' : ∀ g h, z' (g * h) = z' g + W.mat (W.pushRep (algebraMap c.O (PadicAlgCl l)) σ₀) g *ᵥ z' h := by
    intro g h
    have e : W.mat (W.pushRep (algebraMap c.O (PadicAlgCl l)) σ₀) g =
        ((Q⁻¹ * σ g * Q : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) := by
      rw [← hQ']; rfl
    rw [e, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hT, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add]
    exact congrArg (fun v => ((Q⁻¹ : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) *ᵥ v) (hz.2 g h)
  have hσ₁ : Continuous (W.pushRep (algebraMap c.O (PadicAlgCl l)) σ₀) := by
    rw [show (W.pushRep (algebraMap c.O (PadicAlgCl l)) σ₀ : G → _) = fun g => Q⁻¹ * σ g * Q from funext hQ']
    exact (continuous_const.mul hσ).mul continuous_const
  obtain ⟨c', a, hcc, ha, hm⟩ := UpperTheory.V.Th.Det.cocField c _ z' hσ₁ hz' hc'
  obtain ⟨n, b, w, hw, e⟩ := zc_split c c' hcc σ₀ (a • z') (hz'.const_smul a) hm fun g h => by
    simp only [Pi.smul_apply, hc', smul_add, Matrix.mulVec_smul]
  refine ⟨z', ?_, funext hT⟩
  have e' : a • z' = ∑ k, b k • ι (w k) := by
    funext g i
    rw [e, Finset.sum_apply, Finset.sum_apply]
    rfl
  rw [SetLike.mem_coe, ← S.smul_mem_iff ha, e']
  exact S.sum_mem fun k _ => S.smul_mem _ (hS _ (hw k))
