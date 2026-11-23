import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.SymplecticGSp4
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtInSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EptInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OrdLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SplAdjUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CrystallineTransferSurjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.BkAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FrobFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem tb_avg {k G W : Type} [Field k] [CharZero k] [Group G] [AddCommGroup W] [Module k W]
    (a : G → W →ₗ[k] W) (hmul : ∀ g h w, a (g * h) w = a g (a h w)) (f : G → W)
    (hf : ∀ g h, f (g * h) = f g + a g (f h)) (H : Subgroup G) [H.FiniteIndex] (x : W)
    (hx : ∀ h ∈ H, f h = a h x - x) : ∃ y, ∀ g, f g = a g y - y := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set f' : G → W := fun g => f g - (a g x - x) with hf'
  have hc : ∀ g h, f' (g * h) = f' g + a g (f' h) := by
    intro g h
    simp only [hf', hf, hmul, map_sub]
    abel
  have hH : ∀ g h, h ∈ H → f' (g * h) = f' g := by
    intro g h hh
    rw [hc]
    have : f' h = 0 := by simp only [hf', hx h hh, sub_self]
    rw [this, map_zero, add_zero]
  let F : G ⧸ H → W := Quotient.lift f' (by
    intro g g' hgg
    have h1 : g⁻¹ * g' ∈ H := QuotientGroup.leftRel_apply.1 hgg
    have := hH g _ h1
    rw [mul_inv_cancel_left] at this
    exact this.symm)
  have hF : ∀ (g : G) (q : G ⧸ H), F (g • q) = f' g + a g (F q) := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H z => exact hc g z
  set S : W := ∑ q, F q with hS
  have hsum : ∀ g, S = (Fintype.card (G ⧸ H) : k) • f' g + a g S := by
    intro g
    have e1 : ∑ q, F (g • q) = S := Equiv.sum_comp (MulAction.toPerm g) F
    refine e1.symm.trans ?_
    simp only [hF, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← map_sum,
      Nat.cast_smul_eq_nsmul, ← hS]
  have hn : (Fintype.card (G ⧸ H) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨x - (Fintype.card (G ⧸ H) : k)⁻¹ • S, fun g => ?_⟩
  have e : f' g = (Fintype.card (G ⧸ H) : k)⁻¹ • (S - a g S) := by
    rw [eq_inv_smul_iff₀ hn, eq_sub_iff_add_eq]
    exact (hsum g).symm
  have e2 : f g = f' g + (a g x - x) := by simp only [hf', sub_add_cancel]
  rw [e2, e, map_sub, map_smul, smul_sub]
  abel

section Alg

variable {E H : Type} [CommRing E] [Group H]

private def tbSnd (X : M4 (DualNumber E)) : M4 E := Matrix.of fun i j => (X i j).snd

private def tbFst (X : M4 (DualNumber E)) : M4 E := Matrix.of fun i j => (X i j).fst

private theorem tbSnd_mul (X Y : M4 (DualNumber E)) : tbSnd (X * Y) = tbFst X * tbSnd Y + tbSnd X * tbFst Y := by
  ext a b
  simp [tbSnd, tbFst, Matrix.mul_apply, Fin.sum_univ_four, DualNumber.snd_mul]
  ring

private theorem tbFst_mul (X Y : M4 (DualNumber E)) : tbFst (X * Y) = tbFst X * tbFst Y := by
  ext a b
  simp [tbFst, Matrix.mul_apply, Fin.sum_univ_four]

private theorem tbSnd_one : tbSnd (1 : M4 (DualNumber E)) = 0 := by
  ext a b
  by_cases h : a = b <;> simp [tbSnd, Matrix.one_apply, h]

private theorem tb_ad (r : H →* M4 E) (g : H) (X : M4 E) : Loc.adGL r.toHomUnits g X = r g * X * r g⁻¹ := by
  have : ((r.toHomUnits g)⁻¹ : (M4 E)ˣ) = r.toHomUnits g⁻¹ := (map_inv _ _).symm
  show (r.toHomUnits g : M4 E) * X * ((r.toHomUnits g)⁻¹ : (M4 E)ˣ) = _
  rw [this]
  rfl

private theorem tb_coc (r : H →* M4 E) (r' : H →* M4 (DualNumber E)) (h : ∀ g, tbFst (r' g) = r g) (a b : H) :
    tbSnd (r' (a * b)) * r (a * b)⁻¹ =
      tbSnd (r' a) * r a⁻¹ + Loc.adGL r.toHomUnits a (tbSnd (r' b) * r b⁻¹) := by
  rw [tb_ad, map_mul, tbSnd_mul, h, h, mul_inv_rev, map_mul, add_mul, add_comm]
  congr 1
  · rw [mul_assoc, ← mul_assoc (r b), ← map_mul, mul_inv_cancel, map_one, one_mul]
  · simp only [mul_assoc]

private theorem tb_sp (X : M4 (DualNumber E)) (ν : DualNumber E) (hν : ν.snd = 0) (hX : IsGSp ν X) (Y : M4 E)
    (hY : tbFst X * Y = 1) : tbSnd X * Y ∈ sp4 E := by
  have a1 : tbFst (adj X) = adj (tbFst X) := by ext i j; simp [tbFst, adj_apply]
  have a2 : tbSnd (adj X) = adj (tbSnd X) := by ext i j; simp [tbSnd, adj_apply]
  have h1 : adj (tbFst X) * tbFst X = ν.fst • (1 : M4 E) := by
    rw [← a1, ← tbFst_mul, hX]
    ext i j
    by_cases h : i = j <;> simp [tbFst, Matrix.one_apply, h]
  have h2 : adj (tbFst X) * tbSnd X + adj (tbSnd X) * tbFst X = 0 := by
    rw [← a1, ← a2, ← tbSnd_mul, hX]
    ext i j
    by_cases h : i = j <;> simp [tbSnd, Matrix.one_apply, h, hν]
  have h0 : adj (1 : M4 E) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]
  have h3 : adj Y * adj (tbFst X) = 1 := by rw [← Loc.SpFlag.adj_mul, hY, h0]
  have h4 : adj (tbSnd X) = -(adj (tbFst X) * tbSnd X * Y) := by
    have := congrArg (· * Y) h2
    simp only [add_mul, zero_mul, mul_assoc, hY, mul_one] at this
    rw [mul_assoc]
    exact eq_neg_of_add_eq_zero_right this
  show adj _ = -_
  rw [Loc.SpFlag.adj_mul, h4, mul_neg, ← mul_assoc, ← mul_assoc, h3, one_mul]

private theorem tb_tri_diag {A B : M4 E} (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0) (i : Fin 4) :
    (A * B) i i = A i i * B i i :=
  Loc.SpFlag.tri_mul_diag (fun i j h => hA i j h) (fun i j h => hB i j h) i

private theorem tb_chars (r : H →* M4 E) (u : (M4 E)ˣ)
    (h : ∀ g i j, j < i → ((u : M4 E) * r g * (u⁻¹ : (M4 E)ˣ)) i j = 0) :
    ∃ κ : Fin 4 → H →* Eˣ, ∀ g i, ((u : M4 E) * r g * (u⁻¹ : (M4 E)ˣ)) i i = κ i g := by
  let k : Fin 4 → H →* E := fun i =>
    { toFun := fun g => ((u : M4 E) * r g * (u⁻¹ : (M4 E)ˣ)) i i
      map_one' := by simp
      map_mul' := fun a b => by
        rw [← tb_tri_diag (h a) (h b), map_mul]
        simp only [mul_assoc, Units.inv_mul_cancel_left] }
  exact ⟨fun i => (k i).toHomUnits, fun g i => rfl⟩

end Alg

private theorem tb_upper {K : Type} [Field K] (T T' P : M4 K) (hT : ∀ i j, j < i → T i j = 0)
    (hT' : ∀ i j, j < i → T' i j = 0) (hd : ∀ i j, i ≠ j → T i i ≠ T' j j) (h : T * P = P * T') :
    ∀ i j, j < i → P i j = 0 := by
  have e := fun i j => congrFun (congrFun h i) j
  simp only [Matrix.mul_apply, Fin.sum_univ_four] at e
  have t := And.intro (And.intro (hT 1 0 (by decide)) (And.intro (hT 2 0 (by decide)) (hT 3 0 (by decide))))
    (And.intro (hT 2 1 (by decide)) (And.intro (hT 3 1 (by decide)) (hT 3 2 (by decide))))
  have t' := And.intro (And.intro (hT' 1 0 (by decide)) (And.intro (hT' 2 0 (by decide)) (hT' 3 0 (by decide))))
    (And.intro (hT' 2 1 (by decide)) (And.intro (hT' 3 1 (by decide)) (hT' 3 2 (by decide))))
  have k : ∀ i j, i ≠ j → T i i * P i j = P i j * T' j j → P i j = 0 := fun i j hij hh => by
    rw [mul_comm (P i j), ← sub_eq_zero, ← sub_mul, mul_eq_zero, sub_eq_zero] at hh
    exact hh.resolve_left (hd i j hij)
  have p30 : P 3 0 = 0 := k _ _ (by decide) (by simpa only [t, t', zero_mul, mul_zero, add_zero, zero_add] using e 3 0)
  have p31 : P 3 1 = 0 := k _ _ (by decide) (by simpa only [t, t', p30, zero_mul, mul_zero, add_zero, zero_add] using e 3 1)
  have p32 : P 3 2 = 0 := k _ _ (by decide) (by simpa only [t, t', p30, p31, zero_mul, mul_zero, add_zero, zero_add] using e 3 2)
  have p20 : P 2 0 = 0 := k _ _ (by decide) (by simpa only [t, t', p30, zero_mul, mul_zero, add_zero, zero_add] using e 2 0)
  have p21 : P 2 1 = 0 := k _ _ (by decide) (by simpa only [t, t', p20, p31, zero_mul, mul_zero, add_zero, zero_add] using e 2 1)
  have p10 : P 1 0 = 0 := k _ _ (by decide) (by simpa only [t, t', p20, p30, zero_mul, mul_zero, add_zero, zero_add] using e 1 0)
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | assumption | exact absurd hij (by decide)

private theorem tb_uniq {K H : Type} [Field K] (r : H → M4 K) (U U' V V' : M4 K) (hU : U' * U = 1) (hU' : U * U' = 1)
    (hV : V' * V = 1) (h1 : ∀ g i j, j < i → (U * r g * U') i j = 0) (h2 : ∀ g i j, j < i → (V * r g * V') i j = 0) (s : H)
    (hd : ∀ i j, i ≠ j → (U * r s * U') i i ≠ (V * r s * V') j j) (g : H) (i : Fin 4) :
    (U * r g * U') i i = (V * r g * V') i i := by
  have e : ∀ g, (U * r g * U') * (U * V') = (U * V') * (V * r g * V') := fun g => by
    simp only [mul_assoc]
    rw [← mul_assoc U' U, hU, one_mul, ← mul_assoc V' V, hV, one_mul]
  have hP := tb_upper _ _ _ (h1 s) (h2 s) hd (e s)
  have hdet : (U * V').det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero (Matrix.isUnit_det_of_right_inverse hU').ne_zero (Matrix.isUnit_det_of_right_inverse hV).ne_zero
  rw [Matrix.det_of_upperTriangular (fun i j h => hP i j h)] at hdet
  have h3 := congrFun (congrFun (e g) i) i
  rw [tb_tri_diag (h1 g) hP, tb_tri_diag hP (h2 g), mul_comm] at h3
  exact mul_left_cancel₀ (Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)) h3

private theorem tb_sub {l : ℕ} [Fact l.Prime] {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [CommGroup A] (φ : Γ →* Formalism.BasicNotions.Loc.GQ l) (hφ : Continuous φ) (σ : Γ) (hσ : Loc.IsFrob (φ σ)) (χ : Γ →* A)
    (hχ : IsOpen (χ.ker : Set Γ)) :
    ∃ U : Subgroup Γ, U.Normal ∧ IsOpen (U : Set Γ) ∧ σ ∈ U ∧ ∀ g ∈ U, φ g ∈ Loc.Iq l → χ g = 1 := by
  haveI := Subgroup.quotient_finite_of_isOpen _ hχ
  haveI : Finite χ.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange χ).toEquiv
  letI : TopologicalSpace χ.range := ⊥
  haveI : DiscreteTopology χ.range := ⟨rfl⟩
  obtain ⟨f, hf, hfI, hfσ⟩ := Loc.frobFree (φ σ) hσ χ.range (χ.rangeRestrict σ)
  refine ⟨(χ.rangeRestrict * (f.comp φ)⁻¹).ker, inferInstance, ?_, ?_, fun g hg hI => ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := χ.ker ⊓ (f.comp φ).ker) (fun g hg => ?_)
      (hχ.inter ((isOpen_discrete {1}).preimage (hf.comp hφ)))
    have h1 : χ.rangeRestrict g = 1 := Subtype.ext hg.1
    have h2 : f.comp φ g = 1 := hg.2
    rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.inv_apply, h1, h2, inv_one, mul_one]
  · rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, hfσ, mul_inv_cancel]
  · rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, hfI _ hI, inv_one,
      mul_one] at hg
    exact congrArg Subtype.val hg

private theorem tb_loc (hP : Loc.LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] (φ : Γ →* Formalism.BasicNotions.Loc.GQ l) (hφ : Topology.IsOpenEmbedding φ) {E : Type} [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E]
    [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] (r : Γ →* M4 E) (r' : Γ →* M4 (DualNumber E))
    (h : ∀ g, tbFst (r' g) = r g) (hr : Continuous r) (hr' : Continuous fun g => tbSnd (r' g))
    (U : Subgroup Γ) [U.Normal] (hU : IsOpen (U : Set Γ)) (u : (M4 (DualNumber E))ˣ) (κ : Fin 4 → Γ →* (DualNumber E)ˣ)
    (w : Fin 4 → ℤ) (hw : StrictAnti w)
    (h1 : ∀ g i j, j < i → ((u : M4 (DualNumber E)) * r' g * (u⁻¹ : (M4 (DualNumber E))ˣ)) i j = 0)
    (h2 : ∀ g i, ((u : M4 (DualNumber E)) * r' g * (u⁻¹ : (M4 (DualNumber E))ˣ)) i i = κ i g)
    (h3 : ∀ i, ∀ g ∈ U, φ g ∈ Loc.Iq l → κ i g = Loc.cycA l l (DualNumber E) (φ g) ^ w i)
    (h4 : ∀ i j, i < j → ∃ g ∈ U, (κ i g : DualNumber E).fst ≠ (κ j g : DualNumber E).fst * (Loc.cycA l l E (φ g) : E)) :
    (fun g => tbSnd (r' g) * r g⁻¹) ∈ Loc.finiteCocycles φ (Loc.adGL r.toHomUnits) := by
  haveI : IsModuleTopology ℚ_[l] (M4 E) := inferInstanceAs (IsModuleTopology ℚ_[l] (Fin 4 → Fin 4 → E))
  have hri : Continuous fun g => r g⁻¹ := hr.comp continuous_inv
  refine (Loc.pr6 hP φ hφ (Loc.adGL r.toHomUnits) ?_ _ ⟨hr'.matrix_mul hri, tb_coc r r' h⟩ U hU
    (r.toHomUnits.comp U.subtype) (hr.comp continuous_subtype_val) LinearMap.id LinearMap.id (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (r'.toHomUnits.comp U.subtype) (fun g i j => ?_) u
    (fun i => (κ i).comp U.subtype) w (fun g => ⟨h1 g, h2 g⟩) hw (fun i g => h3 i g g.2) fun i j hij => ?_).2.2
  · simp only [ReciprocityTheory.Gal.ContAction, tb_ad]
    exact ((hr.comp continuous_fst).matrix_mul continuous_snd).matrix_mul (hri.comp continuous_fst)
  · refine TrivSqZeroExt.ext (congrFun (congrFun (h g) i) j) ?_
    show tbSnd (r' g) i j = (tbSnd (r' g) * r (g : Γ)⁻¹ * r g) i j
    rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  · obtain ⟨g, hg, hg'⟩ := h4 i j hij
    exact ⟨⟨g, hg⟩, hg'⟩

section Main

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

private theorem tb_cont (D : Raw Ω c) (r' : G ℚ Ω →* M4 (DualNumber (PadicAlgCl l))) (h : D.PtIn _ r') :
    Continuous fun g => tbSnd (r' g) := by
  obtain ⟨R, _, _, _, ρ, y, -, rfl⟩ := h
  have hy := ((coPt c R).2 y).2
  refine continuous_matrix fun i j => ?_
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := hy (ε / 2) (half_pos hε)
  filter_upwards [(ρ.cont i j n).eventually_eq g₀] with g hg
  have h1 := hn _ (Ideal.Quotient.eq.1 hg)
  rw [map_sub, TrivSqZeroExt.snd_sub] at h1
  rw [dist_eq_norm]
  exact h1.trans_lt (half_lt_self hε)

private theorem tb_place (D : Raw Ω c) (hD : D.Good) (K : Type) [CommRing K] [Algebra c.O K] (r : G ℚ Ω →* M4 K)
    (h : D.PtIn K r) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal) :
    ∃ (A : ValuationSubring Ω) (N : Subgroup (G ℚ Ω)), IsPlaceOver A w ∧ IsOpen (N : Set (G ℚ Ω)) ∧
      ∀ g ∈ Ine (F := ℚ) A, g ∈ N → r g = 1 := by
  obtain ⟨-, hu, -, -, hp, -⟩ := ptIn D hD K r h
  obtain ⟨f1, -, -, -, -, -, -, -, -, -, -, f2, -⟩ := facts D hD
  by_cases hS : ∃ p ∈ D.Sb, ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
  · obtain ⟨p, hp1, hp2⟩ := hS
    haveI : Fact p.Prime := ⟨(f1 p hp1).1⟩
    obtain ⟨w', hw', hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := p) (F := ℚ) (D.pl p) (hD.pl_over p Fact.out)
    obtain ⟨j, hj⟩ := (Loc.decEmb (F := ℚ) (Ω := Ω) (v := p)).1 _ w' hAw hw'
    refine ⟨D.pl p, D.ψ.ker, ?_, hD.psi_open, fun g hg hg' => (hp p hp1).2 ⟨g, hg.1⟩ ⟨hg, hg'⟩⟩
    rw [← hj]
    exact ((Loc.iotaFacts j).2.2.2.2.2.1 w).2 hp2
  · refine ⟨placeOf Ω w, D.rbar.ker, isPlaceOver_placeOf Ω w, f2, fun g hg hg' => hu _ (fun p hp hv => ?_) g hg hg'⟩
    have h1 : ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := (isPlaceOver_placeOf Ω w _).1 (by simpa using hv)
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact hw h1
    · exact hS ⟨p, hp, h1⟩

private theorem tb_desc (D : Raw Ω c) (r' : G ℚ Ω →* M4 (DualNumber (PadicAlgCl l))) (h : D.PtIn _ r') :
    ∃ (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (_ : FiniteDimensional ℚ_[l] K) (_ : Algebra c.O K)
      (r₁ : G ℚ Ω →* M4 (DualNumber K)), (∀ a : c.O, ((algebraMap c.O K a : K) : PadicAlgCl l) = a) ∧ D.PtIn _ r₁ ∧
      ∀ g i j, ((r₁ g i j).fst : PadicAlgCl l) = (r' g i j).fst ∧ ((r₁ g i j).snd : PadicAlgCl l) = (r' g i j).snd := by
  obtain ⟨R, _, _, _, ρ, F, hpt, rfl⟩ := h
  obtain ⟨K, hK, hE⟩ := ((coPt c R).2 F).1
  have hO : ∀ x : c.O, algebraMap c.O (PadicAlgCl l) x ∈ K := fun x => by
    have := (hE (algebraMap c.O R x)).1
    rwa [F.commutes] at this
  letI : Algebra c.O ↥K := ((algebraMap c.O (PadicAlgCl l)).codRestrict K hO).toAlgebra
  let F' : R →ₐ[c.O] DualNumber ↥K :=
    { toFun := fun a => ⟨⟨(F a).fst, (hE a).1⟩, ⟨(F a).snd, (hE a).2⟩⟩
      map_one' := TrivSqZeroExt.ext (Subtype.ext (congrArg TrivSqZeroExt.fst (map_one F)))
        (Subtype.ext (congrArg TrivSqZeroExt.snd (map_one F)))
      map_zero' := TrivSqZeroExt.ext (Subtype.ext (congrArg TrivSqZeroExt.fst (map_zero F)))
        (Subtype.ext (congrArg TrivSqZeroExt.snd (map_zero F)))
      map_add' := fun a b => TrivSqZeroExt.ext (Subtype.ext (congrArg TrivSqZeroExt.fst (map_add F a b)))
        (Subtype.ext (congrArg TrivSqZeroExt.snd (map_add F a b)))
      map_mul' := fun a b => TrivSqZeroExt.ext (Subtype.ext (congrArg TrivSqZeroExt.fst (map_mul F a b)))
        (Subtype.ext (congrArg TrivSqZeroExt.snd (map_mul F a b)))
      commutes' := fun c => TrivSqZeroExt.ext (Subtype.ext (congrArg TrivSqZeroExt.fst (F.commutes c)))
        (Subtype.ext (congrArg TrivSqZeroExt.snd (F.commutes c))) }
  exact ⟨K, hK, inferInstance, mapRep (F' : R →+* DualNumber K) ρ.hom, fun _ => rfl,
    ⟨R, inferInstance, inferInstance, inferInstance, ρ, F', hpt, rfl⟩, fun g i j => ⟨rfl, rfl⟩⟩

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
private theorem tb_atL (D : Raw Ω c) (hD : D.Good) (hP : Loc.LocalPublishedTheorems) (r : G ℚ Ω →* M4 (PadicAlgCl l)) (hr : D.EPt r)
    (r' : G ℚ Ω →* M4 (DualNumber (PadicAlgCl l))) (hr' : D.PtIn _ r') (h : ∀ g, tbFst (r' g) = r g)
    (φ : D.Gp l →* Formalism.BasicNotions.Loc.GQ l) (hφ : Topology.IsOpenEmbedding φ)
    (hI : ∀ g, φ g ∈ Loc.Iq l ↔ (g : G ℚ Ω) ∈ D.Ip l) (hc : ∀ g, Loc.cyc l l (φ g) = cycZ ℚ Ω l (g : G ℚ Ω))
    (hF : ∀ g : D.Gp l, (g : G ℚ Ω) = D.sg l → Loc.IsFrob (φ g)) :
    (fun g : D.Gp l => tbSnd (r' g) * r (g : G ℚ Ω)⁻¹) ∈
      Loc.finiteCocycles φ ((Loc.adGL r.toHomUnits).comp (D.Gp l).subtype) := by
  obtain ⟨-, hT, -, hwt, -, -, hinj, -, -, -, -, -, hom, -⟩ := facts D hD
  have hcr := (eptInt D hD r hr).1
  have hcr' := tb_cont D r' hr'
  obtain ⟨K, _, _, r₁, hO, hr₁, he⟩ := tb_desc D r' hr'
  haveI : IsModuleTopology ℚ_[l] ↥K := isModuleTopologyOfFiniteDimensional
  haveI : CompactSpace (D.Gp l) := isCompact_iff_compactSpace.1 (isClosed_Dec _).isCompact
  have hOi : Function.Injective (algebraMap c.O K) := fun a b e => Subtype.ext (by rw [← hO, ← hO, e])
  obtain ⟨-, -, -, ⟨-, hord⟩, -⟩ := ptIn D hD _ r₁ hr₁
  obtain ⟨u, h1, h2⟩ := (ordLocal _ (DualNumber K) _ D.s0 _ hD.decompSigma_mem.1.1 fun i j hij => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, TrivSqZeroExt.fst_sub, sub_ne_zero]
    exact fun e => hij (hinj (hOi e))).1 hord
  obtain ⟨κ, hκ⟩ := tb_chars _ u h1
  let σ : D.Gp l := ⟨D.sg l, (hT l (Finset.mem_insert_self _ _)).1⟩
  obtain ⟨U, hUn, hU, hσ, hUI⟩ := tb_sub φ hφ.continuous σ (hF σ rfl) ((D.ψ.prod D.om).comp (D.Gp l).subtype) (by
    rw [← MonoidHom.comap_ker, MonoidHom.ker_prod]
    exact (hD.psi_open.inter hom).preimage continuous_subtype_val)
  obtain ⟨v, κ', hv, hκI, -, -, -, hne⟩ := Loc.spPtL D hD (r.comp (D.Gp l).subtype) (by
    obtain ⟨R, i1, i2, i3, ρ, y, hpt, rfl⟩ := hr
    exact ⟨R, i1, i2, i3, D.loc ρ l, y, hpt.atL, rfl⟩)
  let π : DualNumber K →+* PadicAlgCl l := (K.val : K →+* PadicAlgCl l).comp (TrivSqZeroExt.fstHom K K K : DualNumber K →+* K)
  have hπ : ∀ g, π.mapMatrix (r₁ g) = r g := fun g => by
    rw [← h]
    ext i j
    exact (he g i j).1
  have hent : ∀ (g : D.Gp l) i j, (π.mapMatrix u.val * r g * π.mapMatrix (u⁻¹).val : M4 (PadicAlgCl l)) i j =
      π (((u : M4 (DualNumber K)) * r₁ g * (u⁻¹ : (M4 (DualNumber K))ˣ)) i j) := fun g i j => by
    rw [← hπ, ← map_mul, ← map_mul]
    rfl
  have hκκ : ∀ i (g : D.Gp l), π (κ i g) = κ' i g := fun i g => by
    have := tb_uniq (fun g : D.Gp l => r g) (π.mapMatrix u.val) (π.mapMatrix (u⁻¹).val)
      (v⁻¹ : (M4 (PadicAlgCl l))ˣ) v (by rw [← map_mul, Units.inv_mul, map_one])
      (by rw [← map_mul, Units.mul_inv, map_one]) v.mul_inv
      (fun g i j hij => (hent g i j).trans ((congrArg π (h1 g i j hij)).trans (map_zero π))) (fun g => (hv g).1) D.s0
      (fun i j hij e => by
        have e1 := (hent D.s0 i i).trans (congrArg π (h2 D.s0 hD.decompSigma_mem.1.1 i))
        have e2 := ((hv D.s0).2 j).trans (hκI j D.s0 hD.decompSigma_mem.1.1)
        exact hij (hinj (Subtype.ext ((hO _).symm.trans (e1.symm.trans (e.trans e2)))))) g i
    exact ((hent g i i).trans (congrArg π (hκ g i))).symm.trans (this.trans ((hv g).2 i))
  let r₀ : G ℚ Ω →* M4 K := mapRep (TrivSqZeroExt.fstHom K K K : DualNumber K →+* K) r₁
  have hr₀ : ∀ g, (r₀ g).map K.val = r g := hπ
  have hs₀ : ∀ g, (tbSnd (r₁ g)).map K.val = tbSnd (r' g) := fun g => by
    ext i j
    exact (he g i j).2
  have hw : StrictAnti fun i => (D.wts4 i : ℤ) := by
    have := hD.two_le
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [Raw.wts4] at hij ⊢ <;> omega
  have key := tb_loc hP φ hφ (r₀.comp (D.Gp l).subtype) (r₁.comp (D.Gp l).subtype) (fun g => rfl)
    (continuous_matrix fun i j => continuous_induced_rng.2 (by
      refine ((hcr.comp (continuous_subtype_val (p := (· ∈ D.Gp l)))).matrix_elem i j).congr fun g => ?_
      exact (congrFun (congrFun (hr₀ g) i) j).symm))
    (continuous_matrix fun i j => continuous_induced_rng.2 (by
      refine ((hcr'.comp (continuous_subtype_val (p := (· ∈ D.Gp l)))).matrix_elem i j).congr fun g => ?_
      exact (he g i j).2.symm))
    U hU u κ _ hw h1 hκ (fun i g hg hgI => by
      have e := hUI g hg hgI
      have e1 : (g : G ℚ Ω) ∈ D.Ip l ⊓ D.ψ.ker ⊓ D.om.ker :=
        ⟨⟨(hI g).1 hgI, congrArg Prod.fst e⟩, congrArg Prod.snd e⟩
      apply Units.ext
      rw [← hκ, h2 g ((hI g).1 hgI), hwt i g e1, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow]
      congr 1
      refine TrivSqZeroExt.ext (Subtype.ext ((hO _).trans ?_)) rfl
      simp only [Loc.cycA, MonoidHom.comp_apply, hc]
      rfl)
    (fun i j hij => by
      obtain ⟨g, hg, hg'⟩ := hne i j hij.ne U hU ⟨σ, hσ, rfl⟩
      refine ⟨g, hg, fun e => hg' ?_⟩
      rw [← hκκ, ← hκκ]
      refine (congrArg K.val e).trans ?_
      rw [map_mul]
      congr 1
      simp only [Loc.cycA, MonoidHom.comp_apply, hc]
      rfl)
  have key2 := Loc.z1fCoef φ _ ((Loc.adGL r.toHomUnits).comp (D.Gp l).subtype) K.val.toLinearMap.mapMatrix
    (continuous_id.matrix_map continuous_subtype_val) (fun g X => by
      rw [tb_ad, MonoidHom.comp_apply (Loc.adGL r.toHomUnits), tb_ad, ← hr₀, ← hr₀]
      exact (Matrix.map_mul (f := (K.val : K →+* PadicAlgCl l))).trans
        (congrArg (· * _) (Matrix.map_mul (f := (K.val : K →+* PadicAlgCl l))))) _ key
  refine cast (congrArg (· ∈ _) (funext fun g => ?_)) key2
  rw [← hr₀, ← hs₀]
  exact Matrix.map_mul (f := (K.val : K →+* PadicAlgCl l))

end Main

theorem UpperTheory.V.GradeZeroInterpolatingElement.tanBK :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → Loc.LocalPublishedTheorems → ∀ r, D.EPt r → ∀ r' : G ℚ Ω →* M4 (DualNumber (PadicAlgCl l)), D.PtIn _ r' → (∀ g i j, (r' g i j).fst = r g i j) → (fun g => (Matrix.of fun i j => (r' g i j).snd) * r g⁻¹) ∈ Z1 (Loc.adGL r.toHomUnits) ∧ Af.IsBK l (Loc.adGL r.toHomUnits) (fun g => (Matrix.of fun i j => (r' g i j).snd) * r g⁻¹) ∧ ∀ g, (Matrix.of fun i j => (r' g i j).snd) * r g⁻¹ ∈ sp4 (PadicAlgCl l) := by
  intro Ω _ _ _ l _ c D hD hP r hr r' hr' h
  have h' : ∀ g, tbFst (r' g) = r g := fun g => Matrix.ext (h g)
  have hZ : (fun g => tbSnd (r' g) * r g⁻¹) ∈ Z1 (Loc.adGL r.toHomUnits) :=
    ⟨(tb_cont D r' hr').matrix_mul ((eptInt D hD r hr).1.comp continuous_inv), tb_coc r r' h'⟩
  refine ⟨hZ, ⟨fun w hw => ?_, fun τ => ?_⟩, fun g => ?_⟩
  · obtain ⟨A, N, hA, hN, h1⟩ := tb_place D hD _ r' hr' w hw
    haveI := Subgroup.quotient_finite_of_isOpen N hN
    haveI : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    obtain ⟨y, hy⟩ := tb_avg (k := PadicAlgCl l) (G := Ine (F := ℚ) A)
      (fun g => Loc.adGL r.toHomUnits g) (fun g h x => by simp)
      (fun g => tbSnd (r' g) * r (g : G ℚ Ω)⁻¹) (fun g h => hZ.2 g h) (N.subgroupOf _) 0 (fun g hg => by
        rw [h1 g g.2 hg, tbSnd_one, zero_mul, map_zero, sub_zero])
    exact ⟨A, hA, y, fun s hs => hy ⟨s, hs⟩⟩
  · obtain ⟨w, hw, hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := l) (F := ℚ) (D.pl l) (hD.pl_over l Fact.out)
    obtain ⟨j, hj⟩ := (Loc.decEmb (F := ℚ) (Ω := Ω) (v := l)).1 _ w hAw hw
    have h1 := ((Loc.decEmb (F := ℚ) (Ω := Ω) (v := l)).2 j).2
    have h2 := (Loc.iotaFacts j).2.2.2.2.2.2
    rw [hj] at h1 h2
    obtain ⟨φ, hφ, a1, -, a2, a3, -⟩ := h1
    refine ⟨j, Subsingleton.elim _ _, (Loc.bkAbove (F := ℚ) j φ (D.Gp l).subtype hφ a1 _ _ hZ).1
      (tb_atL D hD hP r hr r' hr' h' φ hφ a2 (a3 l) fun g hg => (h2 _).2 ?_)⟩
    have e : Loc.iota j (φ g) = D.sg l := AlgEquiv.ext fun y => j.injective (by rw [Loc.iota_spec, a1, hg])
    rw [e]
    exact hD.sg_frob l (Finset.mem_insert_self _ _)
  · exact tb_sp _ _ rfl ((ptIn D hD _ r' hr').1 g) _ (by rw [h', ← map_mul, mul_inv_cancel, map_one])
