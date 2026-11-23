import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.RigPtOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicPointGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkedRig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TNiceSmall

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
  UpperTheory.V.Th
private theorem ap_norm {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (h : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _
private theorem ap_field {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [Algebra ℤ_[l] R] [Module.Finite ℤ_[l] R]
    (φ : R →ₐ[ℤ_[l]] PadicAlgCl l) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ ∀ x, φ x ∈ E ∧ ‖φ x‖ ≤ 1 := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := R)
  haveI := (s.finite_toSet.image φ).to_subtype
  refine ⟨IntermediateField.adjoin ℚ_[l] (φ '' (s : Set R)),
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x, fun x =>
    ⟨?_, ap_norm _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map φ)⟩⟩
  have hx : x ∈ Submodule.span ℤ_[l] (s : Set R) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul a b _ hb =>
    rw [map_smul, ← algebraMap_smul ℚ_[l] a]
    exact IntermediateField.smul_mem _ hb
private theorem ap_coef {l : ℕ} [Fact l.Prime] (c c₁ : Coef l) (A : Subalgebra c.O (PadicAlgCl l)) [Module.Finite c.O A] :
    ∃ c₂ : Coef l, c₁.O ≤ c₂.O ∧ ∀ x ∈ A, x ∈ c₂.O := by
  haveI : Module.Finite ℤ_[l] A := Module.Finite.trans c.O A
  obtain ⟨E₁, f₁, m₁⟩ := ap_field c₁.O.val
  obtain ⟨E₂, f₂, m₂⟩ := ap_field (A.val.restrictScalars ℤ_[l])
  obtain ⟨c₂, hc⟩ := UpperTheory.V.X.So.coefOf l (E₁ ⊔ E₂)
  exact ⟨c₂, fun x hx => (hc x).2 ⟨(le_sup_left : E₁ ≤ E₁ ⊔ E₂) (m₁ ⟨x, hx⟩).1, (m₁ ⟨x, hx⟩).2⟩,
    fun x hx => (hc x).2 ⟨(le_sup_right : E₂ ≤ E₁ ⊔ E₂) (m₂ ⟨x, hx⟩).1, (m₂ ⟨x, hx⟩).2⟩⟩
private theorem ap_local {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [Algebra ℤ_[l] R] (c : Coef l)
    (φ : R →+* c.O) (h1 : ∀ a, φ (algebraMap ℤ_[l] R a) = algebraMap ℤ_[l] c.O a) (hφ : Function.Injective φ) :
    IsLocalHom φ := by
  have hint : φ.IsIntegral := by
    refine RingHom.IsIntegral.tower_top (algebraMap ℤ_[l] R) φ ?_
    rw [show φ.comp (algebraMap ℤ_[l] R) = algebraMap ℤ_[l] c.O from RingHom.ext h1]
    exact fun x => Algebra.IsIntegral.isIntegral x
  exact hint.isLocalHom hφ
private theorem ap_adic {Γ R S : Type} [TopologicalSpace Γ] [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] {f : Γ → R} (h : Alg.AdicCont (maximalIdeal R) f) :
    Alg.AdicCont (maximalIdeal S) fun g => φ (f g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal S ^ N).comap φ := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_comap.2 (map_nonunit φ x hx)) N
  exact (h N).comp (Ideal.quotientMap _ φ hle)
private theorem ap_det {n : ℕ} {A B G H : Type} [CommRing A] [CommRing B] [Group G] [Group H]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (f : A →+* B) (p : H →* G) (τ : H →* Matrix (Fin n) (Fin n) B)
    (h : ∀ g, τ g = (ρ (p g)).map f) : ((W.GDet.ofRep ρ).map f).comap p = W.GDet.ofRep τ := by
  refine W.GDet.ext fun C _ _ x => ?_
  letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra
  change (W.GDet.repAlg ρ C (MonoidAlgebra.mapDomainRingHom C p x)).det = (W.GDet.repAlg τ C x).det
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g r =>
    ext i j
    simp [W.GDet.repAlg, h]
    rfl
private theorem ap_locAlg (hG : GlobalTheory.Published.GlobalArtinReciprocity) {L Ω : Type} [Field L] [NumberField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ka : G L Ω →* (Qbar l)ˣ)
    (hka : Sd.IsAlgChar ι ka) {A : ValuationSubring Ω} {w : W.Plc L} (h : IsPlaceOver A w)
    (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) :
    ∃ wt : W.Emb l w → ℤ, ∀ (m : ℤ) (χ : G L Ω →* (Qbar l)ˣ), IsOpen (χ.ker : Set (G L Ω)) →
      ∀ κ : Dec (F := L) A →* (Qbar l)ˣ,
        (∀ g : Dec (F := L) A, (g : G L Ω) ∈ Ine (F := L) A → κ g = cycBar L Ω l g ^ m * χ g * ka g) →
        W.IsLocAlg h κ fun τ => wt τ - m := by
  obtain ⟨-, art, Y, a, hart, -, hY⟩ := hka
  refine ⟨fun τ => -a ((ι.toRingHom.comp τ.1).comp (algebraMap L (w.adicCompletion L))), fun m χ hχ κ hκ => ?_⟩
  by_cases hl : ∃ b, GlobalTheory.LocLanglands.IsLocalArtin h b
  swap
  · exact ⟨1, by simp, fun b hb => absurd ⟨b, hb⟩ hl⟩
  obtain ⟨ph, h1⟩ := Loc.laHecke h art hart ι Y a ka hY hl
  have h2 := (Loc.laMul h).2.1 _ _ _ m (Loc.laCyc hG h hw)
  have h3 := (Loc.laMul h).2.2 (χ.comp (Dec (F := L) A).subtype) (χ.comp (Ine (F := L) A).subtype)⁻¹
    (Subgroup.isOpen_mono (H₁ := χ.ker.comap (Ine (F := L) A).subtype) (fun x hx => inv_eq_one.2 hx)
      (hχ.preimage continuous_subtype_val)) fun s => mul_inv_cancel _
  have h4 := ((Loc.laMul h).1 _ _ _ _ _ _ ((Loc.laMul h).1 _ _ _ _ _ _ h2 h3).1 h1).1
  refine ⟨_, h4.1, fun b hb s => ?_⟩
  have h5 := h4.2 b hb s
  rw [hκ _ s.2]
  refine Eq.trans ?_ (h5.trans ?_)
  · rfl
  · refine finprod_congr fun τ => ?_
    congr 1
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    ring
private def apExt {l : ℕ} [Fact l.Prime] {k k' : Type} [Field k] [Field k'] {Φ : Fr.Frame l k} {n : ℕ} {K : Type} [CommRing K]
    (f : k →+* k') (ρ : Fr.NRep Φ n K) : Fr.NRep (Φ.ext f) n K := ⟨ρ.r, ρ.ψ, ρ.pol, ρ.diag, ρ.ord⟩
private theorem ap_lift {l : ℕ} [Fact l.Prime] {O O₁ A A₁ : Type} [CommRing O] [IsLocalRing O] [CommRing O₁] [IsLocalRing O₁]
    [CommRing A] [IsLocalRing A] [CommRing A₁] [IsLocalRing A₁] [Algebra O A] [Algebra O₁ A₁]
    [IsLocalHom (algebraMap O A)] [IsLocalHom (algebraMap O₁ A₁)] (f : ResidueField O →+* ResidueField O₁)
    (φ : A →+* A₁) [IsLocalHom φ]
    (h : ∀ a, ResidueField.map (algebraMap O₁ A₁) (f (residue O a)) = residue A₁ (φ (algebraMap O A a)))
    {Φ : Fr.Frame l (ResidueField O)} {n : ℕ} (ρ : Fr.NRep Φ n A) (H : IsLiftA O ρ) :
    IsLiftA O₁ (apExt f (ρ.map φ)) := by
  have h1 : ∀ (x : A) (y : ResidueField O), residue A x = ResidueField.map (algebraMap O A) y →
      residue A₁ (φ x) = ResidueField.map (algebraMap O₁ A₁) (f y) := fun x y e => by
    obtain ⟨a, rfl⟩ := residue_surjective y
    rw [h, ← ResidueField.map_residue φ, e, ResidueField.map_residue, ResidueField.map_residue]
  have h2 : ∀ (u : (ResidueField O)ˣ) (m : ℤ), f (u ^ m).val = (Units.map f.toMonoidHom u ^ m).val := fun u m => by
    rw [← map_zpow]; rfl
  refine ⟨⟨fun i j => ap_adic φ (H.cont.1 i j), fun v i => ap_adic φ (H.cont.2 v i)⟩, ⟨fun g i => ?_, fun v i g => ?_⟩,
    fun g i j hij => ?_⟩
  · exact (h1 _ _ (H.bar.1 g i)).trans (congrArg _ (h2 _ _))
  · exact (h1 _ _ (H.bar.2 v i g)).trans (congrArg _ (h2 _ _))
  · have := h1 (ρ.r g i j) 0 ((H.diag g i j hij).trans (map_zero _).symm)
    rwa [map_zero, map_zero] at this
private theorem rp_psi {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l)
    {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (L : Type) [Field L] [NumberField L] [Algebra L Ω]
    [IsAlgClosure L Ω] (m : ℤ) :
    ∃ χ : G L Ω →* (Qbar l)ˣ, IsOpen (χ.ker : Set (G L Ω)) ∧ (∀ g, χ g ^ Nat.card (ZMod N)ˣ = 1) ∧ ∀ g : G L Ω,
      (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ L Ω g) ^ m).val.1 = (cycBar L Ω l g ^ ((e : ℤ) * m) * χ g).val := by
  let u : c.Oˣ →* (Qbar l)ˣ := Units.map c.O.val.toRingHom.toMonoidHom
  refine ⟨((u.comp (Chr.dirG ℚ Ω ψ)).comp (galEmb ℚ L Ω)) ^ m, ?_, fun g => ?_, fun g => ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := (Chr.cls ℚ Ω N).ker.comap (galEmb ℚ L Ω)) (fun g hg => ?_)
      ((Chr.clsFacts ℚ Ω N).1.preimage (galEmbTop ℚ L Ω).1.continuous)
    have h1 : Chr.cls ℚ Ω N (galEmb ℚ L Ω g) = 1 := hg
    rw [MonoidHom.mem_ker, MonoidHom.zpow_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, Chr.dirG, MonoidHom.comp_apply,
      h1, map_one, map_one, one_zpow]
  · rw [MonoidHom.zpow_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, Chr.dirG, MonoidHom.comp_apply,
      ← map_zpow, ← map_zpow, ← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one]
  · have h1 : u (chiO ℚ Ω l c.O (galEmb ℚ L Ω g)) = cycBar L Ω l g := Units.ext rfl
    change (u _).val = _
    rw [map_zpow, Chr.Psi, MonoidHom.mul_apply, map_mul, MonoidHom.zpow_apply, map_zpow, h1, mul_zpow, ← zpow_mul]
    rfl
private theorem rp_w_ne {k : Type} [Field k] {n : ℕ} (hn : n = 2 ∨ n = 3) (a : kˣ) (ha : a ^ 2 ≠ 1)
    (i j : Fin n) (hij : i ≠ j) : a ^ Fr.w n i ≠ a ^ Fr.w n j := by
  intro h
  have h1 : a ^ (Fr.w n i - Fr.w n j) = 1 := by rw [_root_.zpow_sub, h, mul_inv_cancel]
  have h2 : Fr.w n i - Fr.w n j ∣ 2 := by
    clear h h1
    revert i j
    rcases hn with rfl | rfl <;> decide
  obtain ⟨c, hc⟩ := h2
  apply ha
  have h3 : a ^ (2 : ℤ) = 1 := by rw [hc, _root_.zpow_mul, h1, _root_.one_zpow]
  exact_mod_cast h3
private theorem rp_flag_map {H A K : Type} [Group H] [CommRing A] [CommRing K] {n : ℕ} (j : A →+* K) (r : H →* GL (Fin n) A)
    (ψ : Fin n → H →* Aˣ) (h : W.HasFlag r ψ) : W.HasFlag (W.pushRep j r) fun i => W.pushCh j (ψ i) := by
  obtain ⟨g, hg⟩ := h
  have key : ∀ s a b, (Matrix.GeneralLinearGroup.map j g * W.pushRep j r s * (Matrix.GeneralLinearGroup.map j g)⁻¹ :
      GL (Fin n) K) a b = j ((g * r s * g⁻¹ : GL (Fin n) A) a b) := fun s a b => by
    rw [MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl
  refine ⟨Matrix.GeneralLinearGroup.map j g, fun s => ⟨fun a b hab => ?_, fun a => ?_⟩⟩
  · rw [key, (hg s).1 a b hab, map_zero]
  · rw [key, (hg s).2 a]
    rfl
private theorem rp_flag {l : ℕ} [Fact l.Prime] {O A K : Type} [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A]
    [Algebra O A] [IsLocalHom (algebraMap O A)] [CommRing K] {F : Fr.Frame l (ResidueField O)} {n : ℕ} (hn : n = 2 ∨ n = 3)
    (ρ : Fr.NRep F n A) (H : IsLiftA O ρ) (j : A →+* K) (v : F.V) (g₀ : F.Gv v) (hg : F.Ψ (F.loc v g₀) ^ 2 ≠ 1) :
    W.HasFlag ((ρ.map j).r.comp (F.loc0 v)).toHomUnits ((ρ.map j).ψ v) := by
  have h4 : ∀ i, residue A (ρ.ψ v i g₀) = ResidueField.map (algebraMap O A) (F.Ψ (F.loc v g₀) ^ Fr.w n i).val :=
    fun i => H.bar.2 v i g₀
  have hfl : W.HasFlag (ρ.r.comp (F.loc0 v)).toHomUnits (ρ.ψ v) := by
    refine Fr.flag_loc _ _ g₀ (fun i j hij => ?_) ?_ (fun s => ρ.ord v s)
    · by_contra hu
      have h3 := (residue_eq_zero_iff _).2 hu
      rw [map_sub, h4, h4, sub_eq_zero] at h3
      exact rp_w_ne hn _ hg i j hij (Units.ext ((ResidueField.map (algebraMap O A)).injective h3))
    · have hd : ((ρ.r.comp (F.loc0 v)) g₀).map (residue A) = Matrix.diagonal fun i => residue A (ρ.ψ v i g₀) := by
        ext i j
        by_cases hij : i = j
        · subst hij
          rw [Matrix.diagonal_apply_eq, h4]
          exact H.bar.1 (F.loc0 v g₀) i
        · rw [Matrix.diagonal_apply_ne _ hij]
          exact H.diag (F.loc0 v g₀) i j hij
      rw [hd, Matrix.charpoly_diagonal]
  have h := rp_flag_map j _ _ hfl
  convert h using 1
  · ext g a b
    rfl
  · rfl
private theorem rp_charpoly {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* Matrix (Fin n) (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : W.HasFlag r.toHomUnits κ) (s : H) :
    (r s).charpoly = ∏ i, (Polynomial.X - Polynomial.C (κ i s : k)) := by
  obtain ⟨g, hg⟩ := h
  have h1 := Matrix.charpoly_units_conj g (r s)
  have h2 : ((g * r.toHomUnits s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
    fun i j hij => (hg s).1 i j hij
  have h3 := Matrix.charpoly_of_upperTriangular _ h2
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv, MonoidHom.coe_toHomUnits] at h3
  rw [h3]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h4 := (hg s).2 i
  simp only [Units.val_mul, Matrix.coe_units_inv, MonoidHom.coe_toHomUnits] at h4
  rw [h4]
private theorem rp_free {K : Type} [Field K] {n : ℕ} (α β : Fin n → Kˣ) (a : Kˣ) (hα : FreeRatios α)
    (h : ∏ i, (Polynomial.X - Polynomial.C (β i : K)) = ∏ i, (Polynomial.X - Polynomial.C (α i : K))) :
    FreeRatios fun i => β i * a := by
  have h1 : Function.Injective fun i => (α i : K) := fun i j hij => by
    by_contra hne
    exact hα i j hne 1 one_pos (by rw [pow_one, pow_one]; exact Units.ext hij)
  have h2 : Function.Injective fun i => (β i : K) :=
    Polynomial.separable_prod_X_sub_C_iff.1 (h ▸ Polynomial.separable_prod_X_sub_C_iff.2 h1)
  have h3 : ∀ i, ∃ j, β i = α j := fun i => by
    have h4 := congrArg (Polynomial.eval (β i : K)) h
    rw [Polynomial.eval_prod, Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ i) (by simp)] at h4
    obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 h4.symm
    exact ⟨j, Units.ext (by simpa [sub_eq_zero] using hj)⟩
  choose s hs using h3
  intro i j hij m hm e
  simp only [mul_pow, mul_left_inj, hs] at e
  exact hα _ _ (fun e' => hij (h2 (by simp only [hs, e']))) m hm e
private theorem rp_irr {G H k : Type} [Group G] [Group H] [Field k] {n : ℕ} (a : G → Matrix (Fin n) (Fin n) k)
    (b : H → Matrix (Fin n) (Fin n) k) (π : H → G) (c : H → kˣ)
    (h : ∀ g, a (π g) = (c g : k) • b g) (hb : MatIrr ⊤ b) : MatIrr ⊤ a := by
  intro W hW
  refine hb W fun g _ v hv => ?_
  have h1 := W.smul_mem ((c g)⁻¹ : kˣ) (hW (π g) trivial v hv)
  rwa [h, Matrix.smul_mulVec, smul_smul, Units.inv_mul, one_smul] at h1
private theorem rp_tw_flag {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    {F : Fr.Frame l (ResidueField O)} {n : ℕ} {G : W.GFrame l} {r : W.Resid G O n} (K : TwLink F r)
    {A : Type} [CommRing A] [Algebra O A] (ρ : Fr.NRep F n A) (v : G.Vl)
    (h : W.HasFlag (ρ.r.comp (F.loc0 (K.e v))).toHomUnits (ρ.ψ (K.e v))) :
    W.HasFlag ((K.tw ρ).toHomUnits.comp (G.φ v)) (K.twψ ρ v) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => ?_⟩
  have key : ∀ i j, (g * ((K.tw ρ).toHomUnits.comp (G.φ v)) s * g⁻¹ : GL (Fin n) A) i j =
      ((K.κA A (G.φ v s) : Aˣ) : A) *
        (g * (ρ.r.comp (F.loc0 (K.e v))).toHomUnits (K.lam v s) * g⁻¹ : GL (Fin n) A) i j := fun i j => by
    change ((g : Matrix (Fin n) (Fin n) A) * (((K.κA A (G.φ v s) : Aˣ) : A) • ρ.r (K.π (G.φ v s))) *
      ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)) i j =
      _ * ((g : Matrix (Fin n) (Fin n) A) * ρ.r (F.loc0 (K.e v) (K.lam v s)) *
      ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)) i j
    rw [K.lam_loc, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [key, (hg _).1 i j hij, mul_zero]
  · rw [key, (hg _).2 i, mul_comm]
    rfl
private theorem rp_cont {l : ℕ} [Fact l.Prime] {c₁ c₂ : Coef l}
    {F : Fr.Frame l (ResidueField c₁.O)} {n : ℕ} {G : W.GFrame l} {r : W.Resid G c₁.O n} (K : TwLink F r)
    (ρ : Fr.NRep F n c₂.O) (h : ρ.Cont (maximalIdeal c₂.O)) (j : c₂.O →+* Qbar l) (hj : ∀ a, j a = a.1) :
    Continuous (K.tw (ρ.map j)).toHomUnits := by
  have h1 : Continuous (K.tw (ρ.map j)) := by
    refine continuous_matrix fun a b => ?_
    have h2 := continuous_subtype_val.comp (((X.So.adicCont l c₁).2 _ _).1 K.κ_cont)
    have h3 := (continuous_subtype_val.comp (((X.So.adicCont l c₂).2 _ _).1 (h.1 a b))).comp K.π_cont
    convert h2.mul h3 using 1
    funext g
    exact congrArg (_ * ·) (hj _)
  exact Units.continuous_iff.2 ⟨h1, h1.comp continuous_inv⟩
private theorem rp_val_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : ℕ} (h : a ∣ b)
    (ha : A.valuation (a : Ω) < 1) : A.valuation (b : Ω) < 1 := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  exact mul_lt_one_of_lt_of_le ha ((A.valuation_le_one_iff _).2 (natCast_mem A c))
private theorem rp_unr {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]
    [IsLocalRing O] [Algebra ℤ_[l] O] {N M : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter O N) (h : l * N ∣ M)
    {η : G ℚ Ω →* ℤˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ) (A : ValuationSubring Ω)
    (hA : ¬ A.valuation (M : Ω) < 1) (g : G L Ω) (hg : g ∈ Ine (F := L) A) : k.p0 g = 1 := by
  have hl : ¬ A.valuation (l : Ω) < 1 := fun h' => hA (rp_val_dvd A ((dvd_mul_right l N).trans h) h')
  have hg' : galEmb ℚ L Ω g ∈ Ine (F := ℚ) A := hg
  have h1 : cycZ ℚ Ω l (galEmb ℚ L Ω g) = 1 := (Base.places ℚ Ω l A).2.2.2 hl hg'
  have h2 : Chr.cls ℚ Ω N (galEmb ℚ L Ω g) = 1 :=
    (Chr.clsFacts ℚ Ω N).2.2.2.2 A (fun h' => hA (rp_val_dvd A ((dvd_mul_left N l).trans h) h')) hg'
  have h3 : Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ L Ω g) = 1 := by simp [Chr.Psi, Chr.dirG, chiO, h1, h2]
  refine Subtype.ext ?_
  change toUpl Ω L (W.resP L Ω g) ∈ k.p.ker
  rw [k.p_ker]
  refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨A, hl, hg', ?_, ?_⟩)
  · exact (k.mem_range_resP _).1 ⟨_, rfl⟩
  · exact (congrArg (Units.map (residue O).toMonoidHom) h3).trans (map_one _)
private theorem rp_conj {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) (c : Coef l) (κ : V.frame.G₀ →* c.Oˣ) (m : ℤ)
    (hκ : ∀ g, κ g * κ (V.frame.conj g) = V.frame.eps c.O c.O g ^ m) (ka : G L Ω →* (Qbar l)ˣ)
    (h : ∀ g, (κ (V.pr g)).val.1 = (ka g).val) (g g' : G L Ω) (hg : W.resP L Ω g' = s.c * W.resP L Ω g * s.c⁻¹) :
    ka g * ka g' = cycBar L Ω l g ^ m := by
  let u : c.Oˣ →* (Qbar l)ˣ := Units.map c.O.val.toRingHom.toMonoidHom
  have h0 : ∀ g, u (κ (V.pr g)) = ka g := fun g => Units.ext (h g)
  have h1 : V.frame.conj (V.pr g) = V.pr g' := Subtype.ext (by
    change toGS Ω V.S' s.c * toGS Ω V.S' (W.resP L Ω g) * (toGS Ω V.S' s.c)⁻¹ = toGS Ω V.S' (W.resP L Ω g')
    rw [hg, map_mul, map_mul, map_inv])
  have h3 : V.ε (V.pr g).1 = cycZ L Ω l g := DFunLike.congr_fun V.hε (W.resP L Ω g)
  have h4 : u (V.frame.eps c.O c.O (V.pr g)) = cycBar L Ω l g :=
    Units.ext (congrArg (fun t : ℤ_[l]ˣ => algebraMap ℤ_[l] (Qbar l) t) h3)
  have h2 : κ (V.pr g) * κ (V.pr g') = V.frame.eps c.O c.O (V.pr g) ^ m :=
    (congrArg (fun t => κ (V.pr g) * κ t) h1).symm.trans (hκ _)
  rw [← h0, ← h0, ← h4, ← map_zpow, ← map_mul, h2]
private theorem rp_par {A : Type} [CommGroup A] (t x y z : A) (a b : ℤ) (k : ℕ) (hx : x ^ k = 1) (hy : y ^ k = 1) :
    (t ^ a * x * z / (t ^ b * y * z) * t ^ (b - a)) ^ k = 1 := by
  have h : t ^ a * x * z / (t ^ b * y * z) * t ^ (b - a) = x / y := by
    rw [zpow_sub, mul_div_mul_right_eq_div, mul_div_mul_comm, mul_right_comm, ← div_eq_mul_inv, div_mul_div_cancel, div_self',
      one_mul]
  rw [h, div_pow, hx, hy, div_one]
theorem UpperTheory.V.Th.rigPtOf_alt :
    GlobalTheory.Published.GlobalArtinReciprocity → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → _root_.UpperTheory.V.Th.RigPtOfAlt := by
  intro hG hAd Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k c₁ _ f n ka R hL hka A _ _ _ ρ hρ hψ r hr hirr haut hfree
  obtain ⟨c₂, h₁, h₂⟩ := ap_coef c c₁ A
  letI : Algebra c₁.O c₂.O := (Subalgebra.inclusion h₁).toRingHom.toAlgebra
  let φ : A →+* c₂.O := A.val.toRingHom.codRestrict c₂.O fun x => h₂ x.1 x.2
  haveI : IsLocalHom φ := ap_local c₂ φ (fun a => rfl) fun a b h => Subtype.ext (congrArg (fun t : c₂.O => t.1) h)
  haveI hl : IsLocalHom (algebraMap c₁.O c₂.O) := ap_local c₂ _ (fun a => rfl) (Subalgebra.inclusion_injective h₁)
  obtain ⟨hc, hf, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c₂.O
  haveI : IsCD c₁.O c₂.O := { complete := hc, isLocalHom := hl, fin := hf }
  let j : c₂.O →ₐ[c₁.O] Qbar l := { c₂.O.val.toRingHom with commutes' := fun _ => rfl }
  let ρ₂ : Fr.NRep (Φ.ext f) n c₂.O := apExt f (ρ.map φ)
  have hlift : IsLiftA c₁.O ρ₂ := ap_lift f φ (fun a => by
    rw [R.hf a ⟨a.1, R.le a.2⟩ rfl, ResidueField.map_residue]; rfl) ρ hρ
  obtain ⟨Ph, hPh, -⟩ := phiEx l c₁.O (Φ.ext f) n R.T
  obtain ⟨F, -, hD, hP⟩ := goodPtOf l c₁.O (Φ.ext f) n R.T Ph hPh ⊥ (fun p _ _ => by rw [Ideal.map_bot]; exact bot_le)
    c₂.O ρ₂ hlift (Qbar l) j Subtype.val_injective fun U hU =>
    hirr.2.2 U le_top fun s v hv => by rw [hr]; exact hU (k.p0 s) trivial v hv
  have hAl : ∀ v : W.Vl l L, (R.s.A v).valuation (l : Ω) < 1 := fun v => (natCast_place (R.s.hA v) l).2 v.2
  have hw : ∀ v : W.Vl l L, ((l : ℕ) : 𝓞 L) ∈ (R.s.w v).asIdeal := fun v => (natCast_place (R.s.hw v) l).1 (hAl v)
  choose wt hwt using fun v : W.Vl l L => ap_locAlg hG ι ka hka.alg (R.s.hw v) (hw v)
  choose χ hχ hχN hχe using fun i : Fin n => rp_psi c e ψ L (Ω := Ω) (Fr.w n i)
  let x : R.B₀.Pt := j.comp F
  let ρQ : Fr.NRep (Φ.ext f) n (Qbar l) := ρ₂.map (j : c₂.O →+* Qbar l)
  let ρ0 : R.V.frame.G₀ →* GL (Fin n) (Qbar l) := (R.K.tw ρQ).toHomUnits
  have hrQ : ∀ g, ρQ.r (R.K.π (R.V.pr g)) = W.mat r g := fun g => by
    change _ = (r g).val
    rw [hr, ← R.π_pr]
    rfl
  have hκ : ∀ g, R.K.κA (Qbar l) (R.V.pr g) = ka g := fun g => Units.ext (R.κ_pr g)
  have hpr : ∀ g, W.mat ρ0 (R.V.pr g) = (ka g : Qbar l) • W.mat r g := fun g => by
    rw [← hrQ, ← hκ]
    rfl
  have htw : ρ0.comp R.V.pr = tw r ka := MonoidHom.ext fun g => Units.ext ((hpr g).trans (tw_val r ka g).symm)
  have hx : ∀ v, x.psi v = R.K.twψ ρQ v := fun v => funext fun i => MonoidHom.ext fun g => Units.ext (by
    have h2 : F (R.B₀.u.ψ v i g).val = (R.K.twψ ρ₂ v i g).val := congrArg (fun t => (t g).val) (hP v i)
    change j (F (R.B₀.u.ψ v i g).val) = _
    rw [h2]
    rfl)
  have hxv : ∀ v i g, x.psi v i g = ρQ.ψ (R.K.e v) i (R.K.lam v g) * ka g := fun v i g => by
    rw [hx, ← hκ]
    rfl
  have hin : ∀ (v : W.Vl l L) i (g : Dec (F := L) (R.s.A v)), (g : G L Ω) ∈ Ine (F := L) (R.s.A v) →
      x.psi v i g = cycBar L Ω l g ^ ((e : ℤ) * Fr.w n i) * χ i g * ka g := fun v i g hg => by
    have h3 := hψ (R.K.e v) i (R.K.lam v g) ((R.K.lam_I v g).2 hg)
    rw [R.lam_j] at h3
    rw [hxv]
    congr 1
    refine Units.ext ?_
    rw [← hχe]
    exact congrArg (fun t : A => t.1) h3
  have hanti : StrictAnti fun i => (e : ℤ) * Fr.w n i := fun a b hab => by
    have h1 : Fr.w n b < Fr.w n a := by
      have h2 : (a : ℕ) < b := hab
      unfold Fr.w
      split_ifs <;> omega
    have h3 : (0 : ℤ) < e := by exact_mod_cast H.e_pos
    exact mul_lt_mul_of_pos_left h1 h3
  have hfl : ∀ v, W.HasFlag (ρQ.r.comp ((Φ.ext f).loc0 v)).toHomUnits (ρQ.ψ v) := fun v => by
    obtain ⟨g₀, hg⟩ := R.ok.f3 v
    exact rp_flag R.n23 ρ₂ hlift _ v g₀ hg
  have hV : Nonempty Φ.V := by
    by_contra hV
    rw [not_nonempty_iff] at hV
    have h : _ < Φ.d := R.big.1
    simp [Fr.Frame.d] at h
  obtain ⟨v'⟩ := hV
  have hA : _root_.UpperTheory.V.Th.AutomorphicPointGalois ι x ρ0 := by
    refine ⟨rp_cont R.K ρ₂ hlift.cont _ fun _ => rfl, ?_,
      ⟨fun v i τ => wt v τ - (e : ℤ) * Fr.w n i, fun v τ a b hab => sub_lt_sub_left (hanti hab) _,
        fun v i => hwt v _ (χ i) (hχ i) _ (hin v i)⟩, htw ▸ haut, ?_, fun v => ?_⟩
    · have h1 : W.UniversalOrdinaryDeterminantRing.Pt.D x = (W.GDet.ofRep (R.K.tw ρ₂)).map (j : c₂.O →+* Qbar l) :=
        congrArg (fun D => D.map (j : c₂.O →+* Qbar l)) hD
      refine (congrArg (fun D => D.comap R.V.pr) h1).trans (ap_det _ _ _ _ fun g => ?_)
      rfl
    · rintro _ ⟨g, hg, rfl⟩
      refine Units.ext ((hpr g).trans ?_)
      rw [hka.unr _ R.v0M g hg, ← hrQ, R.π_pr, rp_unr e ψ H.dvd k _ R.v0M g hg]
      exact (one_smul _ _).trans (map_one ρQ.r)
    · exact (hx v).symm ▸ rp_tw_flag R.K ρQ v (hfl _)
  have hN : _root_.UpperTheory.V.Th.AutomorphicPointLocallyGeneric ι x ρ0 := by
    refine _root_.UpperTheory.V.Th.nice_zero_of_rank_two_or_three_irreducible_free ι x ρ0 R.n23 hA (rp_irr _ (W.mat r) R.V.pr ka hpr fun U hU =>
      hirr.2.2 U le_top fun s v hv => hU s trivial v hv) (fun v => ?_) ?_
    · obtain ⟨g, hg, h1, α, hα, h2⟩ := hfree _ (hAl v)
      refine ⟨⟨g, hg⟩, (DFunLike.congr_fun R.V.hε (W.resP L Ω g)).trans h1, ?_⟩
      have h3 := rp_charpoly _ _ (hfl (R.K.e v)) (R.K.lam v ⟨g, hg⟩)
      have h5 := (congrArg ρQ.r (R.K.lam_loc v ⟨g, hg⟩)).trans (hrQ g)
      have h4 := rp_free α _ (ka g) hα (h3.symm.trans ((congrArg Matrix.charpoly h5).trans h2))
      convert h4 using 2 with i
      exact hxv v i ⟨g, hg⟩
    · obtain ⟨v, hv⟩ := R.K.e.surjective v'
      obtain ⟨s, hs⟩ := R.ok.f3 (R.K.e v)
      obtain ⟨g, rfl⟩ := (R.K.lam v).surjective s
      have hn : 1 < n := by have := R.n23; omega
      refine ⟨v, ⟨0, by omega⟩, ⟨1, hn⟩, g, fun h => rp_w_ne R.n23 _ hs ⟨0, by omega⟩ ⟨1, hn⟩ (by simp) ?_⟩
      rw [R.K.psib, R.K.psib, R.K.chib, R.K.chib, ← R.K.lam_loc] at h
      exact mul_right_cancel h
  refine ⟨R.s, R.V, ρ0, hpr, rp_conj R.V c₁ R.K.κ _ R.K.κ_conj ka R.κ_pr, hAd l L Ω R.s R.V R.hV (degEq Ω l ι c N e ψ η σ g₁ B M H L Φ k v').2 c₁ hL n
    (by have := R.n23; omega) (by have := R.n23; omega) R.r R.v0 R.B₀ ι x ρ0 hN
    fun v => ⟨_, Nat.card (ZMod N)ˣ, hanti, Nat.card_pos, fun a b g hg => ?_⟩⟩
  rw [hin v a g hg, hin v b g hg]
  exact rp_par _ _ _ _ _ _ _ (hχN a g) (hχN b g)
end
