import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsLevelProjLevelProj
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
open scoped Topology

namespace GlobalTheory.LBC.Model

section Line

variable {G : Type} [Group G]

theorem hasLevelTrace_line (χ : G →* ℂˣ) {K : Subgroup G} (hK : (K : Set G) ⊆ χ.ker) (A : ℂ →ₗ[ℂ] ℂ) (c : ℂ) :
    HasLevelTrace (ofChar χ) K A c ↔ c = A 1 := by
  have hk : ∀ x : K, χ x = 1 := fun x => hK x.2
  have htop : fixed (ofChar χ) K = ⊤ := by
    ext v; simp [fixed, eig, hk]
  have hbot : twKer (ofChar χ) K 1 = ⊥ := by
    refine Submodule.span_eq_bot.2 ?_
    rintro _ ⟨x, v, rfl⟩
    simp [hk]
  have h1 : Module.finrank ℂ (fixed (ofChar χ) K) = 1 := by
    rw [htop, finrank_top, Module.finrank_self]
  have hT : IsLevelProj (ofChar χ) K A (A 1 • LinearMap.id) := fun v => by
    have : A v = (v : ℂ) * A 1 := by rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
    simp [this, mul_comm]
  have h0 : HasLevelTrace (ofChar χ) K A (A 1) :=
    ⟨inferInstance, _, hT, by simp [h1]⟩
  exact ⟨fun h => h.unique (by simp [hbot]) h0, fun h => h ▸ h0⟩

end Line

section Norm

variable {k k' : Type} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k'] [IsGalois k k']

theorem prod_pow_eq_norm {s : k' ≃ₐ[k] k'} (hs : ∀ t, t ∈ Subgroup.zpowers s) (x : k') :
    ∏ j : Fin (Module.finrank k k'), (s ^ (j : ℕ)) x = algebraMap k k' (Algebra.norm k x) := by
  have ho : orderOf s = Module.finrank k k' := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hs, IsGalois.card_aut_eq_finrank]
  rw [Algebra.norm_eq_prod_automorphisms]
  refine Fintype.prod_bijective (fun j : Fin (Module.finrank k k') => s ^ (j : ℕ)) ?_ _ _ fun _ => rfl
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun i j h => Fin.ext ?_, ?_⟩
  · exact pow_injOn_Iio_orderOf (by rw [ho]; exact i.2) (by rw [ho]; exact j.2) h
  · rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

omit [FiniteDimensional k k'] [IsGalois k k'] in

theorem det_galAct (s : k' ≃ₐ[k] k') {n : ℕ} (g : GL (Fin n) k') :
    (galAct s n g : Matrix (Fin n) (Fin n) k').det = s (g : Matrix (Fin n) (Fin n) k').det :=
  ((s.toAlgHom.toRingHom).map_det (g : Matrix (Fin n) (Fin n) k')).symm

theorem det_norm {s : k' ≃ₐ[k] k'} (hs : ∀ t, t ∈ Subgroup.zpowers s) {n : ℕ} (g : GL (Fin n) k') :
    (norm k s g : Matrix (Fin n) (Fin n) k').det =
      algebraMap k k' (Algebra.norm k (g : Matrix (Fin n) (Fin n) k').det) := by
  rw [← prod_pow_eq_norm hs]
  have h := map_list_prod ((Units.coeHom k').comp (GeneralLinearGroup.det (n := Fin n) (R := k')))
    (List.ofFn fun j : Fin (Module.finrank k k') => galAct (s ^ (j : ℕ)) n g)
  rw [List.map_ofFn, List.prod_ofFn] at h
  refine h.trans (Finset.prod_congr rfl fun j _ => ?_)
  exact det_galAct _ g

theorem det_of_charpoly {s : k' ≃ₐ[k] k'} (hs : ∀ t, t ∈ Subgroup.zpowers s) {n : ℕ} {g : GL (Fin n) k'}
    {γ : GL (Fin n) k} (h : (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k k') =
      (norm k s g : Matrix (Fin n) (Fin n) k').charpoly) :
    GeneralLinearGroup.det γ = Units.map (Algebra.norm k : k' →* k) (GeneralLinearGroup.det g) := by
  ext
  apply (algebraMap k k').injective
  change algebraMap k k' (γ : Matrix (Fin n) (Fin n) k).det =
    algebraMap k k' (Algebra.norm k (g : Matrix (Fin n) (Fin n) k').det)
  rw [← det_norm hs, det_eq_sign_charpoly_coeff, det_eq_sign_charpoly_coeff, ← h]
  simp

end Norm

section Lift

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [Algebra k k']
  [FiniteDimensional k k'] [IsGalois k k']

theorem isLBC_det {s : k' ≃ₐ[k] k'} (hs : ∀ t, t ∈ Subgroup.zpowers s) (n : ℕ) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ)
    (hN : IsSmoothChar (χ.comp (Units.map (Algebra.norm k : k' →* k)))) :
    IsLBC s (detRep (Fin n) χ) (detRep (Fin n) (χ.comp (Units.map (Algebra.norm k : k' →* k)))) := by
  refine ⟨(isSmooth_ofChar_iff _).2 hχ.detChar, isIrreducible_ofChar _, (isSmooth_ofChar_iff _).2 hN.detChar,
    isIrreducible_ofChar _, LinearMap.id, ⟨fun g => ?_, Module.finrank_pos, one_pow _⟩, fun g _ γ h =>
      ⟨χ (GeneralLinearGroup.det γ), ⟨_, hN.detChar.mem_nhds (by simp), fun K _ _ _ hK => ?_⟩,
        ⟨_, hχ.detChar.mem_nhds (by simp), fun K _ _ hK => ?_⟩⟩⟩
  · have : Units.map (Algebra.norm k : k' →* k) (GeneralLinearGroup.det (galAct s n g)) =
        Units.map (Algebra.norm k : k' →* k) (GeneralLinearGroup.det g) := by
      ext
      change Algebra.norm k (galAct s n g : Matrix (Fin n) (Fin n) k').det =
        Algebra.norm k (g : Matrix (Fin n) (Fin n) k').det
      rw [det_galAct, Algebra.norm_eq_of_algEquiv]
    ext
    simp [detRep, this]
  · refine (hasLevelTrace_line _ hK _ _).2 ?_
    simp [detRep, det_of_charpoly hs h]
  · refine (hasLevelTrace_line _ hK _ _).2 ?_
    simp [detRep]

omit [FiniteDimensional k k'] [IsGalois k k'] in

theorem exists_small (n : ℕ) (U : Set (GL (Fin n) k)) (hU : U ∈ 𝓝 (1 : GL (Fin n) k)) :
    ∃ K : Subgroup (GL (Fin n) k), IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧
      (K : Set (GL (Fin n) k)) ⊆ U := by
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k (Fin n) U hU
  exact ⟨J, h1, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

omit [IsGalois k k'] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem exists_small_stable (hc : ∀ t : k' ≃ₐ[k] k', Continuous t) (s : k' ≃ₐ[k] k') (n : ℕ) (U : Set (GL (Fin n) k'))
    (hU : U ∈ 𝓝 (1 : GL (Fin n) k')) :
    ∃ K : Subgroup (GL (Fin n) k'), IsOpen (K : Set (GL (Fin n) k')) ∧ IsCompact (K : Set (GL (Fin n) k')) ∧
      IsStable s K ∧ (K : Set (GL (Fin n) k')) ⊆ U := by
  obtain ⟨J, h1, h2, h3⟩ := exists_small n U hU
  have hcont : ∀ t : k' ≃ₐ[k] k', Continuous (galAct t n) := fun t => by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact Units.continuous_val.matrix_map (hc t)
    · simp only [← map_inv]
      exact Units.continuous_coe_inv.matrix_map (hc t)
  have hmul : ∀ (a b : k' ≃ₐ[k] k') g, galAct a n (galAct b n g) = galAct (a * b) n g := fun a b g => by
    rw [galAct_mul]; rfl
  let K : Subgroup (GL (Fin n) k') := ⨅ t : k' ≃ₐ[k] k', J.comap (galAct t n)
  have hmem : ∀ g, g ∈ K ↔ ∀ t : k' ≃ₐ[k] k', galAct t n g ∈ J := fun g => by simp [K, Subgroup.mem_iInf]
  have ho : IsOpen (K : Set (GL (Fin n) k')) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun t => h1.preimage (hcont t)
  have hle : (K : Set (GL (Fin n) k')) ⊆ J := fun g hg => by simpa using (hmem g).1 hg 1
  refine ⟨K, ho, h2.of_isClosed_subset (K.isClosed_of_isOpen ho) hle, ?_, hle.trans h3⟩
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem _).2 fun t => by rw [hmul]; exact (hmem x).1 hx _
  · intro hg
    exact ⟨galAct s⁻¹ n g, (hmem _).2 fun t => by rw [hmul]; exact (hmem g).1 hg _, by rw [hmul]; simp⟩

theorem eq_of_isLBC (hc : ∀ t : k' ≃ₐ[k] k', Continuous t) {s : k' ≃ₐ[k] k'} (hs : ∀ t, t ∈ Subgroup.zpowers s)
    {χ : kˣ →* ℂˣ} {ψ : k'ˣ →* ℂˣ} (h : IsLBC s (detRep (Fin 1) χ) (detRep (Fin 1) ψ)) :
    ψ = χ.comp (Units.map (Algebra.norm k : k' →* k)) := by
  obtain ⟨h1, -, h2, -, I, -, H⟩ := h
  have h1' := (isSmooth_ofChar_iff _).1 h1
  have h2' := (isSmooth_ofChar_iff _).1 h2
  have hdet : ∀ {F : Type} [Field F] (z : Fˣ), GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) z) = z :=
    fun z => by ext; simp [GeneralLinearGroup.scalar]
  have hchar : ∀ {F : Type} [Field F] (M : Matrix (Fin 1) (Fin 1) F),
      M.charpoly = Polynomial.X - Polynomial.C M.det := fun M => by
    simp [Matrix.charpoly, Matrix.det_unique]
  have key : ∀ z : k'ˣ, (ψ z : ℂ) * I 1 = χ (Units.map (Algebra.norm k : k' →* k) z) := fun z => by
    obtain ⟨c, ⟨U, hU, hU'⟩, ⟨V, hV, hV'⟩⟩ := H (GeneralLinearGroup.scalar (Fin 1) z)
      (by rw [hchar]; exact Polynomial.separable_X_sub_C)
      (GeneralLinearGroup.scalar (Fin 1) (Units.map (Algebra.norm k : k' →* k) z)) (by
        rw [hchar, hchar, det_norm hs]
        simp [GeneralLinearGroup.scalar])
    obtain ⟨K, a1, a2, a3, a4⟩ := exists_small_stable hc s 1 _ (Filter.inter_mem hU (h2'.mem_nhds (by simp)))
    obtain ⟨L, b1, b2, b4⟩ := exists_small 1 _ (Filter.inter_mem hV (h1'.mem_nhds (by simp)))
    have e1 := (hasLevelTrace_line _ (a4.trans Set.inter_subset_right) _ _).1
      (hU' K a1 a2 a3 (a4.trans Set.inter_subset_left))
    have e2 := (hasLevelTrace_line _ (b4.trans Set.inter_subset_right) _ _).1
      (hV' L b1 b2 (b4.trans Set.inter_subset_left))
    simpa [detRep, hdet] using e1.symm.trans e2
  have hI : I 1 = 1 := by simpa using key 1
  ext z
  simpa [hI] using key z

end Lift

section Trivial

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLBC_absPow_iff (s t : ℝ) :
    IsLBC (1 : k ≃ₐ[k] k) (detRep (Fin 1) (absPow k s)) (detRep (Fin 1) (absPow k t)) ↔ s = t := by
  have h1 : ∀ u : k ≃ₐ[k] k, u = 1 := fun u => Subsingleton.elim _ _
  have hs : ∀ u : k ≃ₐ[k] k, u ∈ Subgroup.zpowers (1 : k ≃ₐ[k] k) := fun u => by rw [h1 u]; exact one_mem _
  have hN : ∀ χ : kˣ →* ℂˣ, χ.comp (Units.map (Algebra.norm k : k →* k)) = χ := fun χ => by
    ext z; simp
  constructor
  · intro h
    have e := eq_of_isLBC (fun u => by rw [h1 u]; exact continuous_id) hs h
    rw [hN] at e
    rw [eq_comm, ← sub_eq_zero, ← absPow_ofReal_eq_one (k := k), Complex.ofReal_sub, sub_eq_add_neg, absPow_add,
      absPow_neg, e, mul_inv_cancel]
  · rintro rfl
    have := isLBC_det hs 1 (isSmoothChar_absPow (k := k) s) (by rw [hN]; exact isSmoothChar_absPow _)
    rwa [hN] at this

end Trivial

section Sides

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [Algebra k k']
  {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] in

theorem pow_eq_norm {s : k' ≃ₐ[k] k'} {P : Representation ℂ (GL (Fin n) k') W} {I : W →ₗ[ℂ] W}
    (hI : IsTwInt k s P I) (g : GL (Fin n) k') : (P g * I) ^ Module.finrank k k' = P (norm k s g) := by
  have h1 : ∀ x, I * P x = P (galAct s n x) * I := fun x => (hI.1 x).symm
  have h2 : ∀ (m : ℕ) x, I ^ m * P x = P (galAct (s ^ m) n x) * I ^ m := fun m => by
    induction m with
    | zero => simp
    | succ m ih =>
      intro x
      rw [pow_succ, mul_assoc, h1, ← mul_assoc, ih, pow_succ, galAct_mul, mul_assoc]; rfl
  have h3 : ∀ m : ℕ, (P g * I) ^ m = P (List.ofFn fun j : Fin m => galAct (s ^ (j : ℕ)) n g).prod * I ^ m := fun m => by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ih, List.ofFn_succ_last, List.prod_append, map_mul, mul_assoc, ← mul_assoc (I ^ m), h2]
      simp [pow_succ, mul_assoc]
  rw [h3, hI.2.2, mul_one]; rfl

theorem CharVal_unique {π : Representation ℂ (GL (Fin n) k) V} (hπ : IsSmooth π) {γ : GL (Fin n) k} {c c' : ℂ}
    (h : CharVal π γ c) (h' : CharVal π γ c') : c = c' := by
  obtain ⟨U, hU, H⟩ := h
  obtain ⟨U', hU', H'⟩ := h'
  obtain ⟨K, a1, a2, a4⟩ := exists_small n _ (Filter.inter_mem hU hU')
  exact (H K a1 a2 (a4.trans Set.inter_subset_left)).unique (isCompl_fixed_twKer hπ a2).disjoint
    (H' K a1 a2 (a4.trans Set.inter_subset_right))

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem TwCharVal_unique [FiniteDimensional k k'] (hc : ∀ t : k' ≃ₐ[k] k', Continuous t) {s : k' ≃ₐ[k] k'}
    {P : Representation ℂ (GL (Fin n) k') W} (hP : IsSmooth P) {I : W →ₗ[ℂ] W} {g : GL (Fin n) k'} {c c' : ℂ}
    (h : TwCharVal k s P I g c) (h' : TwCharVal k s P I g c') : c = c' := by
  obtain ⟨U, hU, H⟩ := h
  obtain ⟨U', hU', H'⟩ := h'
  obtain ⟨K, a1, a2, a3, a4⟩ := exists_small_stable hc s n _ (Filter.inter_mem hU hU')
  exact (H K a1 a2 a3 (a4.trans Set.inter_subset_left)).unique (isCompl_fixed_twKer hP a2).disjoint
    (H' K a1 a2 a3 (a4.trans Set.inter_subset_right))

end Sides

end GlobalTheory.LBC.Model
