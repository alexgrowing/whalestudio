import Mathlib
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureExists
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice

noncomputable section

namespace GlobalTheory.AdelicU.Frames

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in

theorem exists_GL_of_components (S : Finset (HeightOneSpectrum (𝓞 F)))
    (b : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (Fv F v ⊗[F] E)) (hb : ∀ v ∉ S, b v = 1)
    (c : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)) :
    ∃ a : GL (Fin n) (AF F ⊗[F] E), (∀ v, bc (compFin F E v) a = b v) ∧ ∀ w, bc (compInf F E w) a = c w := by
  let σ := AlgHom.id F E
  let J : Matrix (Fin n) (Fin n) E := 0
  have hJ : ∀ (R : Type) [CommRing R] [Algebra F R] (g : GL (Fin n) (R ⊗[F] E)), g ∈ HR R σ J := fun R _ _ g => by
    change cT _ g.1 * JR R J * g.1 = JR R J
    simp [J, JR]
  let b' : ∀ v : S, GLoc σ J v := fun v => ⟨b v, hJ _ _⟩
  let c' : ∀ w, GArch σ J w := fun w => ⟨c w, hJ _ _⟩
  have hm := mem_atPts.1 (embAt_mem σ J S b')
  refine ⟨matHom _ σ J (ofInf σ J (embArchPi σ J c') * embAt σ J S b'), fun v => ?_, fun w => ?_⟩
  · rw [← matHom_proj, map_mul, proj_ofInf, one_mul]
    by_cases hv : v ∈ S
    · rw [proj_embAt σ J S b' ⟨v, hv⟩]; rfl
    · rw [hm.2 v hv, map_one, hb v hv]
  · rw [← matHom_projArch, map_mul, projArch_ofInf, projInfArch_embArchPi, mem_finPts_iff_forall.1 hm.1 w, mul_one]
    rfl

omit [NumberField E] in

theorem incl_mem_latLoc {L : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)} {s : 𝓞 F}
    (hs : s ∉ v.asIdeal) {x : Fin n → E} (hx : algebraMap F E s • x ∈ L) :
    (fun i => inclR (Fv F v) (x i)) ∈ latLoc F L v := by
  have hs0 : (s : F) ≠ 0 := fun h => hs (by
    rw [show s = 0 from RingOfIntegers.coe_injective (by simpa using h)]; exact zero_mem _)
  have ha : algebraMap F (Fv F v) (s : F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have h1 : v.valuation F (s : F) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) v).2 hs
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (s : F)⁻¹
    exact (h2.trans ((map_inv₀ _ _).trans ((congrArg _ h1).trans inv_one))).le
  convert tmul_mem_latLoc ha hx using 2 with i
  change (1 : Fv F v) ⊗ₜ[F] x i = _
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Pi.smul_apply, algebraMap_smul, inv_smul_smul₀ hs0]

omit [NumberField E] in

theorem frame_of_rational {L : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)} (P : GL (Fin n) E)
    (h1 : ∀ j, ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ algebraMap F E s • (fun i => P.1 i j) ∈ L)
    (h2 : ∀ x ∈ L, ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ algebraMap F E s • ((P⁻¹).1 *ᵥ x) ∈ stdLattice E n)
    (y : Fin n → Fv F v ⊗[F] E) :
    (∀ i, y i ∈ intLoc F E v) ↔ (bc (inclR (Fv F v)) P).1 *ᵥ y ∈ latLoc F L v := by
  constructor
  · intro hy
    have e : (bc (inclR (Fv F v)) P).1 *ᵥ y =
        ∑ j, (⟨y j, hy j⟩ : intLoc F E v) • fun i => inclR (Fv F v) (P.1 i j) := by
      funext i
      rw [Finset.sum_apply]
      change ∑ j, inclR (Fv F v) (P.1 i j) * y j = ∑ j, y j * inclR (Fv F v) (P.1 i j)
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e]
    refine sum_mem fun j _ => Submodule.smul_mem _ _ ?_
    obtain ⟨s, hs, h⟩ := h1 j
    exact incl_mem_latLoc hs h
  · intro hy
    have key : ∀ z ∈ latLoc F L v, (bc (inclR (Fv F v)) P⁻¹).1 *ᵥ z ∈ latLoc F (stdLattice E n) v := fun z hz => by
      refine latLoc_induction (p := fun z => (bc (inclR (Fv F v)) P⁻¹).1 *ᵥ z ∈ latLoc F (stdLattice E n) v)
        (fun a ha x hx => ?_) (by simp) (fun _ _ h h' => by rw [Matrix.mulVec_add]; exact add_mem h h')
        (fun _ h => by rw [Matrix.mulVec_neg]; exact neg_mem h) hz
      obtain ⟨s, hs, h⟩ := h2 x hx
      convert Submodule.smul_mem _ (⟨_, tmul_mem_intLoc ha 1⟩ : intLoc F E v) (incl_mem_latLoc hs h) using 1
      funext i
      change ∑ j, ((1 : Fv F v) ⊗ₜ[F] (P⁻¹).1 i j) * (a ⊗ₜ[F] x j) =
        (a ⊗ₜ[F] ((1 : 𝓞 E) : E)) * ((1 : Fv F v) ⊗ₜ[F] ∑ j, (P⁻¹).1 i j * x j)
      simp [TensorProduct.tmul_sum, Finset.mul_sum]
    have := key _ hy
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec, mem_latLoc_stdLattice] at this

omit [NumberField F] [NumberField E] in

theorem exists_smul_mem_of_mem_span (M : Submonoid (𝓞 F)) {A : Type} [CommRing A] [Algebra A E]
    (hA : ∀ a : A, ∃ s ∈ M, ∃ r : 𝓞 E, algebraMap F E s * algebraMap A E a = r)
    {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E} (hx : x ∈ Submodule.span A (L : Set (Fin n → E))) :
    ∃ s ∈ M, algebraMap F E s • x ∈ L := by
  have hL : ∀ (s : 𝓞 F), ∀ y ∈ L, algebraMap F E s • y ∈ L := fun s y hy =>
    L.smul_mem (algebraMap (𝓞 F) (𝓞 E) s) hy
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_mem _, hL _ _ hy⟩
  | zero => exact ⟨1, one_mem _, hL _ _ (zero_mem _)⟩
  | add y z _ _ hy hz =>
    obtain ⟨s, hs, hy⟩ := hy
    obtain ⟨t, ht, hz⟩ := hz
    refine ⟨s * t, mul_mem hs ht, ?_⟩
    have := add_mem (hL t _ hy) (hL s _ hz)
    rwa [smul_smul, smul_smul, mul_comm, ← smul_add, ← map_mul, ← map_mul] at this
  | smul a y _ hy =>
    obtain ⟨s, hs, hy⟩ := hy
    obtain ⟨t, ht, r, hr⟩ := hA a
    refine ⟨s * t, mul_mem hs ht, ?_⟩
    have : (r : E) • algebraMap F E s • y ∈ L := L.smul_mem r hy
    convert this using 1
    rw [← hr, ← algebraMap_smul E a y, smul_smul, smul_smul, RingOfIntegers.coe_eq_algebraMap (s * t),
      map_mul, map_mul]
    congr 1
    ring

omit [NumberField F] [NumberField E] in
theorem single_mem_stdLattice (i : Fin n) : (Pi.single i 1 : Fin n → E) ∈ stdLattice E n :=
  fun j _ => ⟨Pi.single (M := fun _ => 𝓞 E) i 1 j, by
    by_cases e : j = i
    · subst e; simp
    · simp [e]⟩

theorem exists_rational_frame (L : Submodule (𝓞 E) (Fin n → E)) [hL : Submodule.IsLattice E L]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ P : GL (Fin n) E,
      (∀ j, ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ algebraMap F E s • (fun i => P.1 i j) ∈ L) ∧
      ∀ x ∈ L, ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ algebraMap F E s • ((P⁻¹).1 *ᵥ x) ∈ stdLattice E n := by
  have hM : Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl ≤ nonZeroDivisors (𝓞 E) :=
    algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ v.asIdeal.primeCompl_le_nonZeroDivisors
  let A : Subalgebra (𝓞 E) E := Localization.subalgebra.ofField E _ hM
  have : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl) A :=
    Localization.subalgebra.isLocalization_ofField E _ _
  have : IsFractionRing A E := Localization.subalgebra.isFractionRing_ofField E _ _
  have : IsDedekindDomain A := IsLocalization.isDedekindDomain (𝓞 E) hM _
  have : IsPrincipalIdealRing A :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 E) v.asIdeal v.ne_bot
  have hA : ∀ a : A, ∃ s ∈ v.asIdeal.primeCompl, ∃ r : 𝓞 E, algebraMap F E s * algebraMap A E a = r := by
    rintro ⟨a, r, _, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨s, hs, r, ?_⟩
    have h0 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) s) ≠ 0 :=
      (map_ne_zero_iff _ RingOfIntegers.coe_injective).2 (nonZeroDivisors.ne_zero (hM ⟨s, hs, rfl⟩))
    exact (mul_comm _ _).trans (inv_mul_cancel_right₀ h0 _)
  set N : Submodule A (Fin n → E) := Submodule.span A (L : Set (Fin n → E)) with hN
  have : Module.Finite A N := by
    obtain ⟨s, hs⟩ := hL.fg
    rw [Module.Finite.iff_fg]
    exact ⟨s, by rw [hN, ← hs, Submodule.span_span_of_tower]⟩
  let b := Module.Free.chooseBasis A N
  let u : Module.Free.ChooseBasisIndex A N → Fin n → E := fun i => (b i : Fin n → E)
  have hli : LinearIndependent E u :=
    (LinearIndependent.iff_fractionRing A E).mp (b.linearIndependent.map' N.subtype N.ker_subtype)
  have hspanA : Submodule.span A (Set.range u) = N := by
    have : Set.range u = N.subtype '' Set.range b := by rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspan : ⊤ ≤ Submodule.span E (Set.range u) := by
    rw [← hL.span_eq_top, Submodule.span_le]
    intro x hx
    have hxN : x ∈ Submodule.span A (Set.range u) := by rw [hspanA]; exact Submodule.subset_span hx
    exact Submodule.span_le_restrictScalars A E _ hxN
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex A N) = n := by
    rw [← Module.finrank_eq_card_basis (Module.Basis.mk hli hspan), Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  let P : Matrix (Fin n) (Fin n) E := Matrix.of fun a j => (u ∘ e.symm) j a
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp (hli.comp _ e.symm.injective)
  refine ⟨hP.unit, fun j => exists_smul_mem_of_mem_span v.asIdeal.primeCompl hA (b (e.symm j)).2, fun x hx =>
    exists_smul_mem_of_mem_span v.asIdeal.primeCompl hA ?_⟩
  have hx' : x ∈ Submodule.span A (Set.range (u ∘ e.symm)) := by
    rw [EquivLike.range_comp, hspanA]; exact Submodule.subset_span hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hx'
  have h1 : x = hP.unit.1 *ᵥ fun j => (c j : E) := by
    rw [← hc]
    funext i
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm (c j : E) (P i j)
  rw [h1, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, ← Finset.univ_sum_single fun j => (c j : E)]
  refine sum_mem fun j _ => ?_
  convert Submodule.smul_mem _ (c j) (Submodule.subset_span (R := A) (single_mem_stdLattice (E := E) j)) using 1
  rw [← Pi.single_smul]
  exact congrArg _ (mul_one _).symm

theorem exists_smul_le {L L' : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG)
    (hL' : Submodule.span E (L' : Set (Fin n → E)) = ⊤) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ x ∈ L, algebraMap F E d • x ∈ L' := by
  have hA : ∀ a : E, ∃ s ∈ nonZeroDivisors (𝓞 F), ∃ r : 𝓞 E, algebraMap F E s * algebraMap E E a = r := fun a => by
    obtain ⟨m, hm, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (Algebra.IsAlgebraic.isAlgebraic a)).exists_integral_multiple
    exact ⟨m, mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hm), ⟨_, hi⟩, by simp⟩
  obtain ⟨t, rfl⟩ := hL
  choose s hs hsx using fun x : Fin n → E =>
    exists_smul_mem_of_mem_span (A := E) (L := L') (x := x) _ hA (hL' ▸ Submodule.mem_top)
  refine ⟨∏ x ∈ t, s x, Finset.prod_ne_zero_iff.2 fun x _ => nonZeroDivisors.ne_zero (hs x), fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem y hy =>
    classical
    rw [← Finset.prod_erase_mul t s hy, RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, mul_smul]
    exact L'.smul_mem (algebraMap (𝓞 F) (𝓞 E) _) (hsx y)
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul a y _ hy => rw [smul_comm]; exact L'.smul_mem a hy

theorem exists_finset_latLoc_eq (L : Submodule (𝓞 E) (Fin n → E)) [hL : Submodule.IsLattice E L] :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, ∀ y, (∀ i, y i ∈ intLoc F E v) ↔ y ∈ latLoc F L v := by
  obtain ⟨d, hd, h⟩ := exists_smul_le (F := F) (L' := L)
    (Submodule.fg_span (Set.finite_range fun j : Fin n => (Pi.single j 1 : Fin n → E))) hL.span_eq_top
  obtain ⟨d', hd', h'⟩ := exists_smul_le (F := F) (L' := stdLattice E n) hL.fg (by
    rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    simpa using single_mem_stdLattice j)
  have hf := Ideal.finite_factors (I := Ideal.span {d * d'}) (by simp [hd, hd'])
  refine ⟨hf.toFinset, fun v hv y => ?_⟩
  have hv' : d * d' ∉ v.asIdeal := fun hc => hv (hf.mem_toFinset.2 (Ideal.dvd_span_singleton.2 hc))
  have := frame_of_rational (L := L) (v := v) 1
    (fun j => ⟨d, fun hc => hv' (Ideal.mul_mem_right _ _ hc), h _ (Submodule.subset_span ⟨j, by
      funext i; simp [Matrix.one_apply, Pi.single_apply]⟩)⟩)
    (fun x hx => ⟨d', fun hc => hv' (Ideal.mul_mem_left _ _ hc), by simpa using h' x hx⟩) y
  rwa [map_one, Units.val_one, Matrix.one_mulVec] at this

theorem exists_isLatticeFrame_of_arch (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L]
    (c : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)) :
    ∃ a : GL (Fin n) (AF F ⊗[F] E), IsLatticeFrame L a ∧ ∀ w, bc (compInf F E w) a = c w := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_latLoc_eq (F := F) L
  choose P h1 h2 using exists_rational_frame (F := F) L
  obtain ⟨a, ha, hc⟩ := exists_GL_of_components S (fun v => if v ∈ S then bc (inclR (Fv F v)) (P v) else 1)
    (fun v hv => if_neg hv) c
  refine ⟨a, fun v y => ?_, hc⟩
  rw [ha v]
  by_cases hv : v ∈ S
  · rw [if_pos hv]; exact frame_of_rational _ (h1 v) (h2 v) y
  · rw [if_neg hv, Units.val_one, Matrix.one_mulVec]; exact hS v hv y

theorem exists_isLatticeFrame (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] :
    ∃ a : GL (Fin n) (AF F ⊗[F] E), IsLatticeFrame L a :=
  (exists_isLatticeFrame_of_arch L fun _ => 1).imp fun _ h => h.1

theorem exists_congr_diagonal_sign {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian) (hd : G.det ≠ 0) :
    ∃ (ε : Fin n → Bool) (Q : GL (Fin n) ℂ), Q.1ᴴ * G * Q.1 = Matrix.diagonal fun i => if ε i then 1 else -1 := by
  have h0 := Formalism.UG.P.eig_ne_zero hG hd.isUnit
  have h1 : (fun i => ((hG.eigenvalues i / |hG.eigenvalues i| : ℝ) : ℂ)) =
      fun i => if decide (0 < hG.eigenvalues i) then 1 else -1 := funext fun i => by
    by_cases h : 0 < hG.eigenvalues i
    · rw [Formalism.UG.P.sign_pos h]; simp [h]
    · rw [Formalism.UG.P.sign_neg (lt_of_le_of_ne (not_lt.1 h) (h0 i))]; simp [h]
  have h2 := Formalism.UG.P.herm_diag hG
  rw [h1] at h2
  set Q := (hG.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal (Formalism.UG.P.scal hG.eigenvalues)
  have h3 : Q.det ≠ 0 := fun h => by
    have := congrArg Matrix.det h2
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_diagonal] at this
    refine Finset.prod_ne_zero_iff.2 (fun i _ => ?_) this.symm
    split_ifs <;> simp
  exact ⟨_, Matrix.GeneralLinearGroup.mkOfDetNeZero Q h3, h2⟩

variable {σ : E →ₐ[F] E}

theorem map_cT_sigR (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w)
    (y : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) :
    (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) y).map (infEmb τ) = (y.map (infEmb τ))ᴴ := by
  ext i j
  exact (infEmb_sigR h τ _).symm

theorem exists_arch_frame (h : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    (w : InfinitePlace F) : ∃ (c : GL (Fin n) (w.Completion ⊗[F] E)) (ε : Fin n → Bool),
      cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) c.1 * JR w.Completion J * c.1 =
        Matrix.diagonal fun i => if ε i then 1 else -1 := by
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  let e := RingEquiv.ofBijective _ (infEmb_bijective h τ)
  have hG : (J.map τ.1).IsHermitian := by
    ext i j
    exact (h.2.2.2 τ.1 _).symm.trans (congrArg _ (hJ.1 i j))
  obtain ⟨ε, Q, hQ⟩ := exists_congr_diagonal_sign hG (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero _).2 hJ.2)
  refine ⟨bc e.symm.toRingHom Q, ε, Matrix.map_injective e.injective ?_⟩
  have h1 : (bc e.symm.toRingHom Q).1.map (infEmb τ) = Q.1 := Matrix.ext fun i j => e.apply_symm_apply _
  have h2 : (JR w.Completion J).map (infEmb τ) = J.map τ.1 := by ext r s; simp [JR, inclR]
  change Matrix.map _ (infEmb τ) = Matrix.map _ (infEmb τ)
  rw [Matrix.map_mul, Matrix.map_mul, map_cT_sigR h, h1, h2, hQ, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  split_ifs <;> simp

theorem continuous_infEmb_symm (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) :
    Continuous (RingEquiv.ofBijective _ (infEmb_bijective h τ)).symm := by
  have := h.1
  have : IsModuleTopology w.Completion (w.Completion ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (w.Completion ⊗[F] E) := IsModuleTopology.isTopologicalRing w.Completion _
  have hr : w.IsReal := IsTotallyReal.isReal w
  let r := InfinitePlace.Completion.isometryEquivRealOfIsReal hr
  have he : ∀ t : ℝ, InfinitePlace.Completion.extensionEmbedding w (r.symm t) = t := fun t =>
    (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hr _).symm.trans (congrArg _ (r.apply_symm_apply t))
  set e := RingEquiv.ofBijective _ (infEmb_bijective h τ)
  have hs : ∀ (t : ℝ) (y : w.Completion ⊗[F] E), e (r.symm t • y) = t * e y := fun t y => by
    rw [Algebra.smul_def, map_mul]
    congr 1
    exact (infEmb_tmul τ _ 1).trans (by rw [map_one, mul_one]; exact he t)
  have : (e.symm : ℂ → _) = fun z => r.symm z.re • (1 : w.Completion ⊗[F] E) + r.symm z.im • e.symm Complex.I := by
    funext z
    apply e.injective
    rw [map_add, hs, hs, map_one, mul_one, e.apply_symm_apply, e.apply_symm_apply, Complex.re_add_im]
  rw [this]
  have h1 : Continuous fun z : ℂ => r.symm z.re := r.symm.continuous.comp Complex.continuous_re
  have h2 : Continuous fun z : ℂ => r.symm z.im := r.symm.continuous.comp Complex.continuous_im
  exact Continuous.fun_add (Continuous.fun_smul h1 continuous_const) (Continuous.fun_smul h2 continuous_const)

theorem isCompact_UJ_one (h : IsCMExt F E σ) (w : InfinitePlace F) :
    IsCompact (UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (1 : Matrix (Fin n) (Fin n) _) :
      Set (GL (Fin n) (w.Completion ⊗[F] E))) := by
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  let e := RingEquiv.ofBijective _ (infEmb_bijective h τ)
  have hc : Continuous fun u : Matrix.unitaryGroup (Fin n) ℂ => bc e.symm.toRingHom (Unitary.toUnits u) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val.matrix_map (continuous_infEmb_symm h τ),
      continuous_subtype_val.star.matrix_map (continuous_infEmb_symm h τ)⟩
  convert isCompact_range hc using 1
  ext g
  constructor
  · intro hg
    have h1 : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) g.1 * 1 * g.1 = 1 := hg
    have h2 := congrArg (fun y => y.map (infEmb τ)) h1
    simp only [mul_one, Matrix.map_mul, map_cT_sigR h, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    exact ⟨⟨_, Matrix.mem_unitaryGroup_iff'.2 h2⟩, Units.ext (Matrix.ext fun i j => e.symm_apply_apply _)⟩
  · rintro ⟨u, rfl⟩
    refine Matrix.map_injective e.injective ?_
    have h1 : (bc e.symm.toRingHom (Unitary.toUnits u)).1.map (infEmb τ) = u.1 :=
      Matrix.ext fun i j => e.apply_symm_apply _
    change Matrix.map _ (infEmb τ) = Matrix.map _ (infEmb τ)
    rw [mul_one, Matrix.map_mul, map_cT_sigR h, h1, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.mem_unitaryGroup_iff'.1 u.2

theorem isCompact_stabArch (h : IsCMExt F E σ) (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F)
    (b : GL (Fin n) (w.Completion ⊗[F] E)) : IsCompact (stabArch σ J w b : Set (GArch σ J w)) := by
  have : IsModuleTopology w.Completion (w.Completion ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (w.Completion ⊗[F] E) := IsModuleTopology.isTopologicalRing w.Completion _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) w.Completion
  have : T2Space (w.Completion ⊗[F] E) := e.isEmbedding.t2Space
  have hcl : IsClosed (HR w.Completion σ J : Set (GL (Fin n) (w.Completion ⊗[F] E))) :=
    isClosed_eq (((Units.continuous_val.matrix_map
      (GlobalTheory.AdelicUnitaryTop.continuous_sigR w.Completion σ)).matrix_transpose.matrix_mul continuous_const).matrix_mul
      Units.continuous_val) continuous_const
  have h1 : Topology.IsClosedEmbedding (matHom w.Completion σ J) := hcl.isClosedEmbedding_subtypeVal
  have h2 := h1.isCompact_preimage
    (((Homeomorph.mulLeft b⁻¹).trans (Homeomorph.mulRight b)).isCompact_preimage.2 (isCompact_UJ_one (n := n) h w))
  convert h2 using 1
  ext g
  exact mem_stabArch

theorem exists_isLatticeFrame_isMajorantFrame (h : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] :
    ∃ a : GL (Fin n) (AF F ⊗[F] E), IsLatticeFrame L a ∧ IsMajorantFrame σ J a := by
  choose c ε hc using exists_arch_frame h hJ
  obtain ⟨a, ha, hw⟩ := exists_isLatticeFrame_of_arch L c
  exact ⟨a, ha, fun w => ⟨ε w, by rw [hw w]; exact hc w⟩⟩

end GlobalTheory.AdelicU.Frames

end
