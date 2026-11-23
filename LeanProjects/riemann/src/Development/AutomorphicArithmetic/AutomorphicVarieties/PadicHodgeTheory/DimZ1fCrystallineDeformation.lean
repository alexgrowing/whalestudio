import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsNeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsIntBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsUniqueUnramifiedCocycleFrobeniusValue
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IqBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdRepBaseLiftApply
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

private theorem dz_pi {E ι M : Type} [Field E] [Fintype ι] [AddCommGroup M] [Module E M]
    {N : Type} [AddCommGroup N] [Module E N] (Φ : N ≃ₗ[E] (ι → M)) (S : ι → Submodule E M) (T : Submodule E N)
    (hT : ∀ x, x ∈ T ↔ ∀ i, Φ x i ∈ S i) (hS : ∀ i, Module.Finite E (S i)) :
    Module.Finite E T ∧ finrank E T = ∑ i, finrank E (S i) := by
  let e : T ≃ₗ[E] (∀ i, S i) :=
    { toFun := fun x i => ⟨Φ x i, (hT _).1 x.2 i⟩
      invFun := fun y => ⟨Φ.symm fun i => y i, (hT _).2 fun i => by simp⟩
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext i; simp }
  exact ⟨Module.Finite.equiv e.symm, by rw [e.finrank_eq, Module.finrank_pi_fintype]⟩

private theorem dz_ch {G E : Type} [Group G] [CommRing E] (κ : G →* Eˣ) (g : G) (x : E) :
    chRep κ g x = (κ g : E) * x := by simp [chRep]

private theorem dz_dec {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E]
    [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E]
    {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V]
    {ι : Type} [Fintype ι] (ρ : Representation E (GQ l) V) (χ : ι → GQ l →* Eˣ) (e : V ≃ₗ[E] (ι → E))
    (he : ∀ g x i, e (ρ g x) i = (χ i g : E) * e x i) (c : GQ l → V) :
    (c ∈ finiteCocycles (MonoidHom.id _) ρ ↔ ∀ i, (fun g => e (c g) i) ∈ finiteCocycles (MonoidHom.id _) (chRep (χ i))) ∧
    (c ∈ B1 ρ ↔ ∀ i, (fun g => e (c g) i) ∈ B1 (chRep (χ i))) ∧
    (c ∈ Z1 ρ → ∀ i, (fun g => e (c g) i) ∈ Z1 (chRep (χ i))) := by
  classical
  refine ⟨⟨fun h i => ?_, fun h => ?_⟩, ⟨fun h i => ?_, fun h => ?_⟩, fun h i => ?_⟩
  · exact (z1fMap _ ρ (chRep (χ i))).2 (((LinearMap.proj i).comp e.toLinearMap).restrictScalars ℚ_[l])
      (fun g x => by simp [he, dz_ch]) c h
  · have h1 : c = ∑ i, fun g => e.symm (Pi.single i (e (c g) i)) := by
      funext g
      rw [Finset.sum_apply, ← map_sum, Finset.univ_sum_single, e.symm_apply_apply]
    rw [h1]
    refine Submodule.sum_mem _ fun i _ => ?_
    refine (z1fMap _ (chRep (χ i)) ρ).2
      ((e.symm.toLinearMap.comp (LinearMap.single E (fun _ => E) i)).restrictScalars ℚ_[l]) (fun g x => ?_) _ (h i)
    apply e.injective
    funext k
    by_cases hk : k = i
    · subst hk; simp [he, dz_ch]
    · simp [he, hk]
  · obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 h
    exact (mem_coboundaries1 _ _).2 ⟨e m i, fun g => by simp [hm g, he, dz_ch]⟩
  · choose m hm using fun i => (mem_coboundaries1 _ _).1 (h i)
    refine (mem_coboundaries1 _ _).2 ⟨e.symm m, fun g => e.injective (funext fun i => ?_)⟩
    simpa [he, dz_ch] using hm i g
  · have hc : Continuous (((LinearMap.proj i).comp e.toLinearMap).restrictScalars ℚ_[l] : V →ₗ[ℚ_[l]] E) :=
      IsModuleTopology.continuous_of_linearMap _
    exact ⟨hc.comp h.1, fun g k => by simp [h.2 g k, he, dz_ch]⟩

private theorem dz_cont {G E : Type} [Group G] [TopologicalSpace G] [CommRing E] [TopologicalSpace E]
    [IsTopologicalRing E] (κ : G →* Eˣ) (hκ : Continuous fun g => (κ g : E)) : ContAction (chRep κ) := by
  have : (fun p : G × E => chRep κ p.1 p.2) = fun p => (κ p.1 : E) * p.2 := by
    funext p; simp [chRep]
  unfold ReciprocityTheory.Gal.ContAction
  rw [this]
  exact (hκ.comp continuous_fst).mul continuous_snd

private theorem dz_unr (hP : LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E]
    [Module.Finite ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E]
    (κ : GQ l →* Eˣ) (hκ : Continuous fun g => (κ g : E)) (hI : ∀ g ∈ Iq l, κ g = 1) :
    (∀ c ∈ Z1 (chRep κ), c ∈ finiteCocycles (MonoidHom.id _) (chRep κ) ↔ ∀ g ∈ Iq l, c g = 0) ∧
    Module.Finite E (finiteCocycles (MonoidHom.id _) (chRep κ)) ∧ finrank E (finiteCocycles (MonoidHom.id _) (chRep κ)) = 1 := by
  have hI' : ∀ g ∈ Iq l, chRep κ g = 1 := fun g hg => by ext; simp [dz_ch, hI g hg]
  have h1 := z1fUnr hP (MonoidHom.id (GQ l)) Topology.IsOpenEmbedding.id (chRep κ) (dz_cont κ hκ) hI'
  refine ⟨h1, ?_⟩
  obtain ⟨σ, hσ⟩ := (iqBasic l).2.2.2.1
  have h2 := existsUnique_unramified_cocycle_frobenius_value (l := l) (chRep κ) (dz_cont κ hκ) hI' σ hσ
  let f : finiteCocycles (MonoidHom.id _) (chRep κ) →ₗ[E] E := (LinearMap.proj σ).comp (Submodule.subtype _)
  have hf : Function.Bijective f := by
    refine ⟨fun c c' h => Subtype.ext ?_, fun x => ?_⟩
    · exact (h2 (c'.1 σ)).unique ⟨c.2.1, (h1 _ c.2.1).1 c.2, h⟩ ⟨c'.2.1, (h1 _ c'.2.1).1 c'.2, rfl⟩
    · obtain ⟨c, hc, hc', hx⟩ := (h2 x).exists
      exact ⟨⟨c, (h1 c hc).2 hc'⟩, hx⟩
  let e := LinearEquiv.ofBijective f hf
  exact ⟨Module.Finite.equiv e.symm, by rw [e.finrank_eq, finrank_self]⟩

private def dzS (E : Type) [Field E] (p : Fin 3 × Fin 3) : E :=
  if p.1.val + p.2.val < 2 then 1 else if p.1.val + p.2.val = 2 then 0 else -1

private noncomputable def dzE (E : Type) [Field E] [CharZero E] : Matrix (Fin 3) (Fin 3) E ≃ₗ[E] (Fin 3 × Fin 3 → E) where
  toFun X p := X p.1 p.2 + dzS E p * X p.2.rev p.1.rev
  invFun y := Matrix.of fun a b => (1 + dzS E (a, b) ^ 2)⁻¹ * (y (a, b) - dzS E (a, b) * y (b.rev, a.rev))
  map_add' X Y := by funext p; simp; ring
  map_smul' c X := by funext p; simp; ring
  left_inv X := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [dzS, Fin.rev] <;> ring
  right_inv y := by
    funext ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> simp [dzS, Fin.rev] <;> ring

private theorem dzE_apply {E : Type} [Field E] [CharZero E] (X : Matrix (Fin 3) (Fin 3) E) (p : Fin 3 × Fin 3) :
    dzE E X p = X p.1 p.2 + dzS E p * X p.2.rev p.1.rev := rfl

private theorem dz_wt (a b : Fin 3) : wt b.rev a.rev = wt a b := by
  revert a b; decide

private theorem dz_gw {E : Type} [Field E] [CharZero E] (X : Matrix (Fin 3) (Fin 3) E) (j : ℤ) :
    X ∈ gw E j ↔ ∀ p : Fin 3 × Fin 3, wt p.1 p.2 ≠ j → dzE E X p = 0 := by
  refine ⟨fun h p hp => ?_, fun h a b hp => ?_⟩
  · rw [dzE_apply, h _ _ hp, h _ _ (by rwa [dz_wt])]; simp
  · rw [← (dzE E).symm_apply_apply X]
    change _ * (dzE E X (a, b) - _ * dzE E X (b.rev, a.rev)) = 0
    rw [h (a, b) hp, h (b.rev, a.rev) (by rwa [dz_wt])]; simp

private def dzChi {G E : Type} [Group G] [Field E] (η : G →* ℤˣ) (κ : G →* Eˣ) (p : Fin 3 × Fin 3) : G →* Eˣ :=
  κ ^ wt p.1 p.2 * if p.1.val + p.2.val ≤ 2 then (Units.map (Int.castRingHom E : ℤ →* E)).comp η else 1

private theorem dz_eq {G E : Type} [Group G] [Field E] [CharZero E] (η : G →* ℤˣ) (κ : G →* Eˣ) (g : G)
    (X : Matrix (Fin 3) (Fin 3) E) (p : Fin 3 × Fin 3) :
    dzE E (adRep (r0 η κ) g X) p = (dzChi η κ p g : E) * dzE E X p := by
  obtain ⟨a, b⟩ := p
  simp only [dzE_apply, adRep_baseLift_apply, dz_wt, dzChi, MonoidHom.mul_apply, MonoidHom.zpow_apply, Units.val_mul]
  generalize ((κ g ^ wt a b : Eˣ) : E) = t
  rcases Int.units_eq_one_or (η g) with h | h <;>
    fin_cases a <;> fin_cases b <;> simp [dzS, Fin.rev, h] <;> ring

private theorem dz_data {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O)
    (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E]
    [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E]
    [IsTopologicalRing E] (κ : GQ l →* Eˣ) (hκ : κ = (Units.map (algebraMap O E : O →* E)).comp D.Ψ) :
    D.rz E = r0 D.η κ ∧ ∀ p : Fin 3 × Fin 3, Continuous (fun g => (dzChi D.η κ p g : E)) ∧
      HasWeight (MonoidHom.id _) (dzChi D.η κ p) (D.e * wt p.1 p.2) ∧
      (wt p.1 p.2 = 0 → ∀ g ∈ Iq l, dzChi D.η κ p g = 1) := by
  have h1 : Continuous fun g => (κ g : E) := by
    have h := (ptCont (l := l) O E (Algebra.ofId O E)).1 _ _ D.Ψ_cont
    unfold QCont at h
    rw [← eq_moduleTopology ℚ_[l] E] at h
    subst hκ
    exact h
  have h2 : Continuous κ := Units.continuous_iff.2 ⟨h1, by
    simpa only [map_inv, Function.comp_def] using h1.comp continuous_inv⟩
  have h3 : Continuous ((Units.map (Int.castRingHom E : ℤ →* E)).comp D.η) := by
    have ho : IsOpen (D.η.ker : Set (GQ l)) := by
      have : D.η.ker = GK D.Kv := Subgroup.ext fun g => D.η_ker g
      rw [this]
      haveI := D.Kv.2
      exact D.Kv.1.fixingSubgroup_isOpen
    refine continuous_of_continuousAt_one _ ?_
    refine (continuousAt_const (y := 1)).congr ?_
    filter_upwards [ho.mem_nhds D.η.ker.one_mem] with g hg
    have hg' : D.η g = 1 := hg
    simp [hg']
  have h4 : ∀ (p : Fin 3 × Fin 3), ∀ g ∈ Iq l, dzChi D.η κ p g = κ g ^ wt p.1 p.2 := by
    intro p g hg
    unfold dzChi
    split_ifs <;> simp [D.η_unr g hg]
  refine ⟨?_, fun p => ⟨?_, ⟨D.τ.ker, D.τ_open, fun g hg hI => ?_⟩, fun h g hg => by rw [h4 p g hg, h, zpow_zero]⟩⟩
  · subst hκ
    refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl
    change (tor O (D.Ψ g) : Matrix (Fin 3) (Fin 3) O).map (algebraMap O E) = tor E _
    rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    rw [MonoidHom.comp_apply, ← map_zpow (Units.map (algebraMap O E : O →* E))]
    rfl
  · refine Units.continuous_val.comp ?_
    unfold dzChi
    split_ifs
    · exact (h2.zpow _).mul h3
    · exact (h2.zpow _).mul continuous_const
  · have hg' : D.τ g = 1 := hg
    have h5 : κ g = cycA l l E g ^ D.e := by
      subst hκ
      rw [MonoidHom.comp_apply, D.Ψ_I g hI, hg', mul_one, map_pow]
      congr 1
      exact Units.ext (IsScalarTower.algebraMap_apply ℤ_[l] O E _).symm
    rw [h4 p g hI, h5, zpow_mul, zpow_natCast]
    rfl

private theorem dz_sum (j : ℤ) :
    ∑ p : Fin 3 × Fin 3, (if wt p.1 p.2 = j then (if 0 < wt p.1 p.2 then 2 else 1) else 0) = locDims j := by
  by_cases h : -2 ≤ j ∧ j ≤ 2
  · obtain ⟨h1, h2⟩ := h
    interval_cases j <;> decide
  · have hw : ∀ p : Fin 3 × Fin 3, -2 ≤ wt p.1 p.2 ∧ wt p.1 p.2 ≤ 2 := by decide
    rw [Finset.sum_eq_zero fun p _ => if_neg fun (hp : wt p.1 p.2 = j) => h (hp ▸ hw p)]
    unfold locDims
    split_ifs <;> omega

theorem UpperTheory.V.Loc.dim_Z1f_crystalline_deformation :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] (j : ℤ), Module.Finite E ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E))) ∧ finrank E ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E)) ⊓ Submodule.pi Set.univ fun _ => gw E j) = locDims j ∧ (∀ γ ∈ finiteCocycles (MonoidHom.id _) (adRep (D.rz E)), (fun g => Matrix.of fun a b => if wt a b = j then γ g a b else 0) ∈ finiteCocycles (MonoidHom.id _) (adRep (D.rz E))) ∧ ∀ γ ∈ Z1 (adRep (D.rz E)), (∀ g, γ g ∈ gw E j) → (j < 0 → (γ ∈ finiteCocycles (MonoidHom.id _) (adRep (D.rz E)) ↔ γ ∈ B1 (adRep (D.rz E)))) ∧ (j = 0 → (γ ∈ finiteCocycles (MonoidHom.id _) (adRep (D.rz E)) ↔ ∀ g ∈ Iq l, γ g = 0)) := by
  intro hP l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ _ _ j
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective
  haveI : IsModuleTopology ℚ_[l] (Matrix (Fin 3) (Fin 3) E) :=
    inferInstanceAs (IsModuleTopology ℚ_[l] (Fin 3 → Fin 3 → E))
  obtain ⟨hr, hχ⟩ := dz_data D E _ rfl
  rw [hr]
  set κ := (Units.map (algebraMap O E : O →* E)).comp D.Ψ
  set χ := dzChi D.η κ
  have hd := dz_dec (adRep (r0 D.η κ)) χ (dzE E) (dz_eq D.η κ)
  have he : (0 : ℤ) < D.e := by exact_mod_cast D.e_pos
  have hch := fun p => z1fChar hP (MonoidHom.id (GQ l)) Topology.IsOpenEmbedding.id (χ p) (hχ p).1 _ (hχ p).2.1
  have hun := fun p hp => dz_unr hP (χ p) (hχ p).1 ((hχ p).2.2 hp)
  have hdim : ∀ p, Module.Finite E (finiteCocycles (MonoidHom.id _) (chRep (χ p))) ∧
      finrank E (finiteCocycles (MonoidHom.id _) (chRep (χ p))) = if 0 < wt p.1 p.2 then 2 else 1 := by
    intro p
    rcases lt_trichotomy (wt p.1 p.2) 0 with h | h | h
    · obtain ⟨h1, h2⟩ := (hch p).1 (mul_neg_of_pos_of_neg he h)
      rw [h1, h2, if_neg h.le.not_gt]
      exact ⟨by unfold ReciprocityTheory.Gal.B1; infer_instance, rfl⟩
    · rw [if_neg h.le.not_gt]
      exact (hun p h).2
    · obtain ⟨h1, h2⟩ := (hch p).2 (mul_pos he h)
      rw [if_pos h, h2, MonoidHom.range_eq_top.2 Function.surjective_id, Subgroup.index_top]
      exact ⟨h1, rfl⟩
  let Φ : (GQ l → Matrix (Fin 3) (Fin 3) E) ≃ₗ[E] (Fin 3 × Fin 3 → GQ l → E) :=
    (LinearEquiv.piCongrRight fun _ => dzE E).trans
      { Equiv.piComm _ with map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hΦ : ∀ c p, Φ c p = fun g => dzE E (c g) p := fun _ _ => rfl
  refine ⟨(dz_pi Φ _ _ (fun c => (hd c).1) fun p => (hdim p).1).1, ?_, fun γ hγ => ?_, fun γ hγ hg => ?_⟩
  · rw [← dz_sum, (dz_pi Φ (fun p => if wt p.1 p.2 = j then finiteCocycles (MonoidHom.id _) (chRep (χ p)) else ⊥) _
      (fun c => ?_) fun p => ?_).2]
    · refine Finset.sum_congr rfl fun p _ => ?_
      by_cases h : wt p.1 p.2 = j
      · rw [if_pos h, if_pos h, (hdim p).2]
      · rw [if_neg h, if_neg h, finrank_bot]
    · rw [Submodule.mem_inf, (hd c).1, Submodule.mem_pi]
      simp only [dz_gw, hΦ]
      refine ⟨fun h p => ?_, fun h => ⟨fun p => ?_, fun g _ p hp => ?_⟩⟩
      · split_ifs with hp
        · exact h.1 p
        · exact funext fun g => h.2 g trivial p hp
      · have := h p
        split_ifs at this with hp
        · exact this
        · exact SetLike.le_def.1 bot_le this
      · have := h p
        rw [if_neg hp] at this
        exact congrFun this g
    · by_cases h : wt p.1 p.2 = j
      · rw [if_pos h]; exact (hdim p).1
      · rw [if_neg h]; infer_instance
  · rw [(hd _).1] at hγ ⊢
    intro p
    by_cases h : wt p.1 p.2 = j
    · simpa only [dzE_apply, Matrix.of_apply, dz_wt, if_pos h] using hγ p
    · simp only [dzE_apply, Matrix.of_apply, dz_wt, if_neg h, mul_zero, add_zero]
      exact Submodule.zero_mem _
  · have h0 : ∀ p : Fin 3 × Fin 3, wt p.1 p.2 ≠ j → (fun g => dzE E (γ g) p) = 0 :=
      fun p hp => funext fun g => (dz_gw _ _).1 (hg g) p hp
    refine ⟨fun hj => ?_, fun hj => ?_⟩
    · rw [(hd _).1, (hd _).2.1]
      refine forall_congr' fun p => ?_
      by_cases h : wt p.1 p.2 = j
      · rw [((hch p).1 (mul_neg_of_pos_of_neg he (h ▸ hj))).1]
      · rw [h0 p h]; simp
    · have h1 : (∀ g ∈ Iq l, γ g = 0) ↔ ∀ p, ∀ g ∈ Iq l, dzE E (γ g) p = 0 :=
        ⟨fun h p g hg => by rw [h g hg, map_zero]; rfl,
          fun h g hg => (dzE E).map_eq_zero_iff.1 (funext fun p => h p g hg)⟩
      rw [(hd _).1, h1]
      refine forall_congr' fun p => ?_
      by_cases h : wt p.1 p.2 = j
      · exact (hun p (h.trans hj)).1 _ ((hd γ).2.2 hγ p)
      · exact ⟨fun _ g _ => congrFun (h0 p h) g, fun _ => by rw [h0 p h]; exact Submodule.zero_mem _⟩
