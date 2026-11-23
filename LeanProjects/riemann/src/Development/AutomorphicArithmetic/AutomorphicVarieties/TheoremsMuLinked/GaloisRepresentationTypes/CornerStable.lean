import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.ContinuousSubActions.ContActionSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DualInclUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SnocZeroLastCoordinateLast
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsNeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsIntBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap

namespace UpperTheory.V.Th.OrdinaryBlock

open Formalism.BasicNotions.Loc ReciprocityTheory.Gal Topology UpperTheory.V.Loc

section Alg

variable {G E : Type} [Group G] [Field E] {n : ℕ} {r : G →* GL (Fin n) E} {κ : Fin n → G →* Eˣ}

private theorem ad_apply (r : G →* GL (Fin n) E) (g : G) (X : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    adGL r g X i j = ∑ b, ∑ a, (r g : Matrix (Fin n) (Fin n) E) i a * X a b * (r g⁻¹ : Matrix (Fin n) (Fin n) E) b j := by
  change ((r g : Matrix (Fin n) (Fin n) E) * X * ((r g)⁻¹ : GL (Fin n) E)) i j = _
  rw [← map_inv]
  simp only [Matrix.mul_apply, Finset.sum_mul]

private theorem ad_entry (h : UpperTri r κ) (g : G) (X : Matrix (Fin n) (Fin n) E) (i j : Fin n)
    (hX : ∀ a b, i ≤ a → b ≤ j → (a, b) ≠ (i, j) → X a b = 0) :
    adGL r g X i j = ((κ i * (κ j)⁻¹) g : Eˣ) * X i j := by
  have key : ∀ a b, (a, b) ≠ (i, j) →
      (r g : Matrix (Fin n) (Fin n) E) i a * X a b * (r g⁻¹ : Matrix (Fin n) (Fin n) E) b j = 0 := by
    intro a b hab
    rcases lt_or_ge a i with h1 | h1
    · rw [(h g).1 i a h1, zero_mul, zero_mul]
    rcases lt_or_ge j b with h2 | h2
    · rw [(h g⁻¹).1 b j h2, mul_zero]
    rw [hX a b h1 h2 hab, mul_zero, zero_mul]
  rw [ad_apply, Finset.sum_eq_single j (fun b _ hb => Finset.sum_eq_zero fun a _ => key a b fun e => hb (Prod.ext_iff.1 e).2)
    (fun e => absurd (Finset.mem_univ _) e), Finset.sum_eq_single i (fun a _ ha => key a j fun e => ha (Prod.ext_iff.1 e).1)
    (fun e => absurd (Finset.mem_univ _) e),
    (h g).2, (h g⁻¹).2]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_inv, Units.val_mul]
  ring

private def corner (E : Type) [Field E] {n : ℕ} (i j : Fin n) : Submodule E (Matrix (Fin n) (Fin n) E) where
  carrier := {X | ∀ a b, i ≤ a → b ≤ j → (a, b) ≠ (i, j) → X a b = 0}
  zero_mem' := fun _ _ _ _ _ => rfl
  add_mem' := fun hx hy a b h1 h2 h3 => by simp [hx a b h1 h2 h3, hy a b h1 h2 h3]
  smul_mem' := fun c x hx a b h1 h2 h3 => by simp [hx a b h1 h2 h3]

private theorem corner_stable (h : UpperTri r κ) (i j : Fin n) (g : G) :
    corner E i j ≤ (corner E i j).comap (adGL r g) := by
  intro X hX a b h1 h2 h3
  rw [ad_entry h g X a b, hX a b h1 h2 h3, mul_zero]
  intro c d h4 h5 _
  refine hX c d (h1.trans h4) (h5.trans h2) fun e => h3 ?_
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 e
  rw [le_antisymm h1 h4, le_antisymm h5 h2]

end Alg

section Fin

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {φ : G →* GQ l}
  {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E]
  [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] [T2Space E] {n : ℕ} {r : G →* GL (Fin n) E}
  {κ : Fin n → G →* Eˣ}

omit [T2Space E] in
private theorem cont_ad (hr : Continuous fun g => (r g : Matrix (Fin n) (Fin n) E)) : ContAction (adGL r) := by
  have hi : Continuous (fun g => (((r g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) := by
    simp only [← map_inv]
    exact hr.comp continuous_inv
  exact ((hr.comp continuous_fst).matrix_mul continuous_snd).matrix_mul (hi.comp continuous_fst)

private theorem entry (hφ : IsOpenEmbedding φ) (hr : Continuous fun g => (r g : Matrix (Fin n) (Fin n) E))
    (h : UpperTri r κ) (U : Subgroup G) [U.Normal] (hU : IsOpen (U : Set G)) (hcr : CrOn φ (adGL r) U)
    (y : G → Matrix (Fin n) (Fin n) E) (hy : y ∈ finiteCocycles φ (adGL r)) (i j : Fin n) (hm : ∀ g, y g ∈ corner E i j) :
    (fun g => y g i j) ∈ finiteCocycles φ (chRep (κ i * (κ j)⁻¹)) := by
  haveI : IsModuleTopology ℚ_[l] (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (IsModuleTopology ℚ_[l] (Fin n → Fin n → E))
  haveI : ContinuousSMul ℚ_[l] (Matrix (Fin n) (Fin n) E) := IsModuleTopology.toContinuousSMul _ _
  haveI : FiniteDimensional ℚ_[l] (corner E i j) :=
    Module.Finite.of_injective ((corner E i j).subtype.restrictScalars ℚ_[l]) Subtype.val_injective
  haveI : ContinuousSMul ℚ_[l] (corner E i j) :=
    ⟨continuous_induced_rng.2 (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))⟩
  haveI : IsModuleTopology ℚ_[l] (corner E i j) := isModuleTopologyOfFiniteDimensional
  let σ := (adGL r).subrepresentation (corner E i j) (corner_stable h i j)
  have hσ : ContAction σ := continuous_induced_rng.2
    ((cont_ad hr).comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  let c : G → corner E i j := fun g => ⟨y g, hm g⟩
  have hc : c ∈ Z1 σ := ⟨continuous_induced_rng.2 hy.1.1, fun g k => Subtype.ext (hy.1.2 g k)⟩
  have h1 := z1fSub φ hφ σ (adGL r) hσ (cont_ad hr) (corner E i j).subtype (fun _ _ => rfl) Subtype.val_injective
    U hU hcr c hc hy
  exact (z1fMap φ σ (chRep (κ i * (κ j)⁻¹))).2
    (((Matrix.entryLinearMap E E i j).comp (corner E i j).subtype).restrictScalars ℚ_[l])
    (fun g x => ad_entry h g x i j x.2) c h1

omit [T2Space E] in
private theorem crOn_ad (P : LocalPublishedTheorems) (hφ : IsOpenEmbedding φ)
    (hr : Continuous fun g => (r g : Matrix (Fin n) (Fin n) E)) (h : UpperTri r κ) (w : Fin n → ℤ) (hw : StrictAnti w)
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (hI : ∀ i, ∀ g ∈ U, φ g ∈ Iq l → κ i g = cycA l l E (φ g) ^ w i)
    (hne : ∀ i j, i < j → ∃ g ∈ U, (κ i g : E) ≠ κ j g * (cycA l l E (φ g) : E)) : CrOn φ (adGL r) U := by
  haveI : IsModuleTopology ℚ_[l] (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (IsModuleTopology ℚ_[l] (Fin n → Fin n → E))
  have hφU : IsOpenEmbedding (φ.comp U.subtype) := hφ.comp hU.isOpenEmbedding_subtypeVal
  have hr1 : Continuous fun g : U => (r.comp U.subtype g : Matrix (Fin n) (Fin n) E) := hr.comp continuous_subtype_val
  have h1 : IsCr (φ.comp U.subtype) (colRep (r.comp U.subtype)) :=
    prC P _ hφU (AlgHom.id E E) (fun a ha => ⟨1, by simpa using ha⟩) (r.comp U.subtype)
      (fun i j => by
        unfold QCont
        rw [← IsModuleTopology.eq_moduleTopology' (R := ℚ_[l]) (A := E)]
        exact hr1.matrix_elem i j)
      (fun i => (κ i).comp U.subtype) w (fun g => h g) hw (fun i g hg => hI i g g.2 hg)
      (fun i j hij => by
        obtain ⟨g, hg, e⟩ := hne i j hij
        exact ⟨⟨g, hg⟩, e⟩)
  have hc : ContAction (colRep (r.comp U.subtype)) := (hr1.comp continuous_fst).matrix_mulVec continuous_snd
  refine (isCrys_isDR_internalHom _ hφU _ _ (adGL (r.comp U.subtype)) hc hc (cont_ad hr1)
    ((Matrix.mulVecBilin E E).restrictScalars₁₂ ℚ_[l] ℚ_[l]) (fun g X x => ?_) (fun X Y e => ?_)).1 h1 h1
  · change Matrix.mulVec ((r g : Matrix (Fin n) (Fin n) E) * X * (((r g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
      (Matrix.mulVec (r g : Matrix (Fin n) (Fin n) E) x) = Matrix.mulVec (r g : Matrix (Fin n) (Fin n) E) (X.mulVec x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  · exact Matrix.ext_of_mulVec_single fun i => LinearMap.congr_fun e _

private theorem fin (P : LocalPublishedTheorems) (hφ : IsOpenEmbedding φ)
    (hr : Continuous fun g => (r g : Matrix (Fin n) (Fin n) E)) (h : UpperTri r κ) (w : Fin n → ℤ) (hw : StrictAnti w)
    (U : Subgroup G) [U.Normal] (hU : IsOpen (U : Set G))
    (hI : ∀ i, ∀ g ∈ U, φ g ∈ Iq l → κ i g = cycA l l E (φ g) ^ w i)
    (hne : ∀ i j, i < j → ∃ g ∈ U, (κ i g : E) ≠ κ j g * (cycA l l E (φ g) : E))
    (y : G → Matrix (Fin n) (Fin n) E) (hy : y ∈ finiteCocycles φ (adGL r)) :
    ∃ X, ∀ g, (∀ i j, j < i → (y g - (adGL r g X - X)) i j = 0) ∧
      (φ g ∈ Iq l → ∀ i, (y g - (adGL r g X - X)) i i = 0) := by
  haveI : IsModuleTopology ℚ_[l] (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (IsModuleTopology ℚ_[l] (Fin n → Fin n → E))
  have hcr := crOn_ad P hφ hr h w hw U hU hI hne
  have hκ : ∀ i, Continuous fun g => (κ i g : E) := fun i => by
    simp only [← fun g => (h g).2 i]
    exact hr.matrix_elem i i
  have hκ2 : ∀ i j, Continuous fun g => ((κ i * (κ j)⁻¹) g : E) := fun i j => by
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, ← map_inv, Units.val_mul]
    exact (hκ i).mul ((hκ j).comp continuous_inv)
  have hsub : ∀ X, (fun g => y g - (adGL r g X - X)) ∈ finiteCocycles φ (adGL r) := fun X =>
    sub_mem hy ((z1fMap φ (adGL r) (adGL r)).1 (cont_ad hr) ((mem_coboundaries1 _ _).2 ⟨X, fun _ => rfl⟩))
  have key : ∀ s : Finset (Fin n × Fin n), (∀ p ∈ s, p.2 < p.1) →
      (∀ p ∈ s, ∀ a b, p.1 ≤ a → b ≤ p.2 → (a, b) ∈ s) →
      ∃ X, ∀ g, ∀ p ∈ s, (y g - (adGL r g X - X)) p.1 p.2 = 0 := by
    intro s
    induction s using Finset.induction_on_max_value (fun p : Fin n × Fin n => (p.2.val : ℤ) - p.1.val) with
    | empty => exact fun _ _ => ⟨0, fun _ p hp => absurd hp (Finset.notMem_empty _)⟩
    | insert p s hp hmax ih =>
      obtain ⟨i, j⟩ := p
      intro hlow hcl
      have hup : ∀ q ∈ s, q.1 ≤ i → j ≤ q.2 → False := fun q hq h1 h2 => by
        have h3 := hmax q hq
        rw [Fin.le_def] at h1 h2
        refine hp ?_
        rwa [show (i, j) = q from Prod.ext (Fin.ext (by simp only at h3 ⊢; omega)) (Fin.ext (by simp only at h3 ⊢; omega))]
      obtain ⟨X, hX⟩ := ih (fun q hq => hlow q (Finset.mem_insert_of_mem hq)) fun q hq a b h1 h2 =>
        (Finset.mem_insert.1 (hcl q (Finset.mem_insert_of_mem hq) a b h1 h2)).resolve_left fun e => by
          obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 e
          exact hup q hq h1 h2
      have hji : j < i := hlow _ (Finset.mem_insert_self _ _)
      have h1 := entry hφ hr h U hU hcr _ (hsub X) i j fun g a b h1 h2 h3 =>
        hX g (a, b) ((Finset.mem_insert.1 (hcl _ (Finset.mem_insert_self _ _) a b h1 h2)).resolve_left h3)
      rw [((z1fChar P φ hφ _ (hκ2 i j) (w i - w j) ⟨U, hU, fun g hg hg' => by
        rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hI i g hg hg', hI j g hg hg', zpow_sub]⟩).1
        (sub_neg.2 (hw hji))).1, mem_coboundaries1] at h1
      obtain ⟨m, hm⟩ := h1
      refine ⟨X + Matrix.single i j m, fun g q hq => ?_⟩
      have e : (y g - (adGL r g (X + Matrix.single i j m) - (X + Matrix.single i j m))) q.1 q.2 =
          (y g - (adGL r g X - X)) q.1 q.2 - (adGL r g (Matrix.single i j m) q.1 q.2 - Matrix.single i j m q.1 q.2) := by
        simp only [map_add, Matrix.sub_apply, Matrix.add_apply]
        ring
      rw [e]
      rcases Finset.mem_insert.1 hq with rfl | hq
      · rw [ad_entry h g _ i j fun a b _ _ h3 => Matrix.single_apply_of_ne _ _ _ _ _ fun e => h3 (by rw [e.1, e.2]),
          Matrix.single_apply_same, sub_eq_zero]
        exact hm g
      · have h0 : ∀ a b, q.1 ≤ a → b ≤ q.2 → Matrix.single i j m a b = 0 := fun a b h1 h2 =>
          Matrix.single_apply_of_ne _ _ _ _ _ fun e => hup q hq (e.1 ▸ h1) (e.2 ▸ h2)
        rw [hX g q hq, ad_entry h g _ _ _ fun a b h1 h2 _ => h0 a b h1 h2, h0 _ _ le_rfl le_rfl]
        simp
  obtain ⟨X, hX⟩ := key (Finset.univ.filter fun p => p.2 < p.1) (fun p hp => (Finset.mem_filter.1 hp).2)
    fun p hp a b h1 h2 => Finset.mem_filter.2 ⟨Finset.mem_univ _,
      (h2.trans_lt (Finset.mem_filter.1 hp).2).trans_le h1⟩
  have hX' : ∀ g i j, j < i → (y g - (adGL r g X - X)) i j = 0 := fun g i j hij =>
    hX g (i, j) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hij⟩)
  refine ⟨X, fun g => ⟨hX' g, fun hg i => ?_⟩⟩
  have h1 := entry hφ hr h U hU hcr _ (hsub X) i i fun g a b h1 h2 h3 =>
    hX' g a b (lt_of_le_of_ne (h2.trans h1) fun e => h3 (by
      subst e
      rw [le_antisymm h2 h1]))
  exact (z1fUnr P φ hφ (chRep (κ i * (κ i)⁻¹)) (((hκ2 i i).comp continuous_fst).mul continuous_snd)
    (fun g _ => LinearMap.ext fun x => by simp [chRep]) _ h1.1).1 h1 g hg

end Fin

open TensorProduct in
private theorem tmul_one_inj {k V B : Type} [Field k] [AddCommGroup V] [Module k V] [CommRing B] [Algebra k B]
    (hB : Nontrivial B) {v w : V} (h : v ⊗ₜ[k] (1 : B) = w ⊗ₜ[k] (1 : B)) : v = w := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k B)
    (LinearMap.ker_eq_bot.2 (algebraMap k B).injective)
  have h1 : π 1 = 1 := by simpa using LinearMap.congr_fun hπ 1
  simpa [h1] using congrArg (fun x => TensorProduct.rid k V (LinearMap.lTensor V π x)) h

section Bar

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {φ : G →* GQ l} {n : ℕ}

open TensorProduct in
private theorem desc [T2Space G] (r : G →* GL (Fin n) (PadicAlgCl l))
    (hr : Continuous fun g => (r g).val)
    (y : G → Matrix (Fin n) (Fin n) (PadicAlgCl l)) (hy : y ∈ finiteCocycles φ (adGL r)) :
    ∃ (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (_ : FiniteDimensional ℚ_[l] E) (s : G →* GL (Fin n) E)
      (z : G → Matrix (Fin n) (Fin n) E),
      (∀ g, (s g).val.map E.val = (r g).val) ∧
      (∀ g X, (adGL s g X).map E.val = adGL r g (X.map E.val)) ∧
      (∀ g, (z g).map E.val = y g) ∧ z ∈ finiteCocycles φ (adGL s) := by
  obtain ⟨E₀, _, hE₀⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l G n r fun i j => hr.matrix_elem i j
  obtain ⟨⟨hcc, hcoc⟩, x, hx⟩ := hy
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  obtain ⟨T⟩ := tiedP l
  have hB : Nontrivial (Bcr l) := (GlobalTheory.RegularRing.isDomain_of_tied T (botExt l)).toNontrivial
  let t : Set (PadicAlgCl l) := Set.range fun p : S × Fin n × Fin n => p.1.1.1 p.2.1 p.2.2
  haveI : Finite t := (Set.finite_range _).to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] t) :=
    IntermediateField.finiteDimensional_adjoin fun z _ => (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  let E : IntermediateField ℚ_[l] (PadicAlgCl l) := E₀ ⊔ IntermediateField.adjoin ℚ_[l] t
  have hrE : ∀ g a b, (r g).val a b ∈ E := fun g a b =>
    (le_sup_left : E₀ ≤ E) (hE₀ g a b)
  have hS : ∀ p ∈ S, ∀ a b, p.1 a b ∈ E := fun p hp a b =>
    (le_sup_right : _ ≤ E) (IntermediateField.subset_adjoin _ _ ⟨(⟨p, hp⟩, a, b), rfl⟩)
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap E (PadicAlgCl l))
    (LinearMap.ker_eq_bot.2 (algebraMap E (PadicAlgCl l)).injective)
  have hπ1 : ∀ y : E, π (y : PadicAlgCl l) = y := fun y => LinearMap.congr_fun hπ y
  have hπ2 : ∀ (c : E) y, π (c * y) = c * π y := fun c y => map_smul π c y
  have hinj : Function.Injective fun X : Matrix (Fin n) (Fin n) E => X.map E.val :=
    Matrix.map_injective Subtype.val_injective
  let s : G →* GL (Fin n) E := MonoidHom.toHomUnits
    { toFun := fun g => Matrix.of fun a b => (⟨_, hrE g a b⟩ : E)
      map_one' := hinj (by
        simp only []
        rw [Matrix.map_one _ (map_zero _) (map_one _)]
        exact congrArg Units.val (map_one r))
      map_mul' := fun g h => hinj (by
        simp only []
        rw [Matrix.map_mul]
        change (r (g * h)).val = (r g).val * (r h).val
        rw [map_mul, Units.val_mul]) }
  have hs : ∀ g, (s g).val.map E.val = (r g).val :=
    fun g => rfl
  have hs' : ∀ g a b, (r g).val a b = ((s g).val a b : E) :=
    fun g a b => rfl
  let f : Matrix (Fin n) (Fin n) (PadicAlgCl l) →ₗ[ℚ_[l]] Matrix (Fin n) (Fin n) E :=
    (π.restrictScalars ℚ_[l]).mapMatrix
  let i : Matrix (Fin n) (Fin n) E →ₗ[ℚ_[l]] Matrix (Fin n) (Fin n) (PadicAlgCl l) := E.val.toLinearMap.mapMatrix
  have hf : ∀ g X, f (adGL r g X) = adGL s g (f X) := fun g X => by
    ext1 a b
    change π (adGL r g X a b) = _
    rw [ad_apply, ad_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hs', hs', mul_comm, hπ2, hπ2, mul_comm]
    rfl
  have hi : ∀ g X, i (adGL s g X) = adGL r g (i X) := fun g X => by
    ext1 a b
    change E.val (adGL s g X a b) = _
    rw [ad_apply, ad_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_mul, map_mul]
    rfl
  have key : ∀ g (y : Matrix (Fin n) (Fin n) (PadicAlgCl l) ⊗[ℚ_[l]] Bcr l),
      LinearMap.rTensor (Bcr l) f (actC φ (adGL r) g y) = actC φ (adGL s) g (LinearMap.rTensor (Bcr l) f y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [actC, hf]
    | add a b ha hb => simp only [map_add, ha, hb]
  have key' : ∀ g (y : Matrix (Fin n) (Fin n) E ⊗[ℚ_[l]] Bcr l),
      LinearMap.rTensor (Bcr l) i (actC φ (adGL s) g y) = actC φ (adGL r) g (LinearMap.rTensor (Bcr l) i y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [actC, hi]
    | add a b ha hb => simp only [map_add, ha, hb]
  set x := ∑ p ∈ S, p.1 ⊗ₜ[ℚ_[l]] p.2 with hxd
  have hix : LinearMap.rTensor (Bcr l) i (LinearMap.rTensor (Bcr l) f x) = x := by
    rw [hxd, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    congr 1
    ext1 a b
    exact congrArg Subtype.val (hπ1 ⟨p.1 a b, hS p hp a b⟩)
  have hx' : ∀ g, f (y g) ⊗ₜ[ℚ_[l]] (1 : Bcr l) =
      actC φ (adGL s) g (LinearMap.rTensor (Bcr l) f x) - LinearMap.rTensor (Bcr l) f x := fun g => by
    rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
  have hcE : ∀ g, (f (y g)).map E.val = y g := fun g => by
    have h1 := congrArg (LinearMap.rTensor (Bcr l) i) (hx' g)
    rw [map_sub, key', hix, ← hx g, LinearMap.rTensor_tmul] at h1
    exact tmul_one_inj hB h1
  refine ⟨E, inferInstance, s, fun g => f (y g), hs, hi, hcE, ⟨?_, fun g h => ?_⟩, _, hx'⟩
  · refine continuous_matrix fun a b => continuous_induced_rng.2 ((hcc.matrix_elem a b).congr fun g => ?_)
    exact (congrFun (congrFun (hcE g) a) b).symm
  · exact (congrArg f (hcoc g h)).trans (by rw [map_add, hf])

private theorem bar (P : LocalPublishedTheorems) (hφ : IsOpenEmbedding φ) {r : G →* GL (Fin n) (PadicAlgCl l)}
    {κ : Fin n → G →* (PadicAlgCl l)ˣ}
    (hr : Continuous fun g => (r g).val) (h : UpperTri r κ) (w : Fin n → ℤ)
    (hw : StrictAnti w) (U : Subgroup G) [U.Normal] (hU : IsOpen (U : Set G))
    (hI : ∀ i, ∀ g ∈ U, φ g ∈ Iq l → κ i g = cycA l l (PadicAlgCl l) (φ g) ^ w i)
    (hne : ∀ i j, i < j → ∃ g ∈ U, (κ i g : PadicAlgCl l) ≠ κ j g * (cycA l l (PadicAlgCl l) (φ g) : PadicAlgCl l))
    (y : G → Matrix (Fin n) (Fin n) (PadicAlgCl l)) (hy : y ∈ finiteCocycles φ (adGL r)) :
    ∃ X, ∀ g, (∀ i j, j < i → (y g - (adGL r g X - X)) i j = 0) ∧
      (φ g ∈ Iq l → ∀ i, (y g - (adGL r g X - X)) i i = 0) := by
  haveI : T2Space G := hφ.isEmbedding.t2Space
  obtain ⟨E, _, s, z, hs, had, hz, hzf⟩ := desc r hr y hy
  haveI : IsModuleTopology ℚ_[l] ↥E := isModuleTopologyOfFiniteDimensional
  have hs' : ∀ g a b, ((s g).val a b : PadicAlgCl l) =
      (r g).val a b := fun g a b => congrFun (congrFun (hs g) a) b
  have hκE : ∀ i g, (κ i g : PadicAlgCl l) ∈ E := fun i g => by
    rw [← (h g).2 i, ← hs']
    exact SetLike.coe_mem _
  let κ' : Fin n → G →* Eˣ := fun i => MonoidHom.toHomUnits
    { toFun := fun g => ⟨κ i g, hκE i g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp) }
  have hc : ∀ σ, ((cycA l l E σ : E) : PadicAlgCl l) = cycA l l (PadicAlgCl l) σ := fun σ => rfl
  obtain ⟨X, hX⟩ := fin (κ := κ') P hφ
    (continuous_matrix fun a b => continuous_induced_rng.2 ((hr.matrix_elem a b).congr fun g => (hs' g a b).symm))
    (fun g => ⟨fun a b hab => Subtype.ext ((hs' g a b).trans ((h g).1 a b hab)),
      fun a => Subtype.ext ((hs' g a a).trans ((h g).2 a))⟩) w hw U hU
    (fun i g hg hg' => Units.ext (Subtype.ext (by
      change (κ i g : PadicAlgCl l) = E.val _
      rw [hI i g hg hg', Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀]
      rfl)))
    (fun i j hij => by
      obtain ⟨g, hg, e⟩ := hne i j hij
      exact ⟨g, hg, fun e' => e (congrArg Subtype.val e')⟩) z hzf
  have e : ∀ g a b, (y g - (adGL r g (X.map E.val) - X.map E.val)) a b = E.val ((z g - (adGL s g X - X)) a b) := by
    intro g a b
    rw [← had, ← hz]
    simp only [Matrix.sub_apply, Matrix.map_apply, map_sub]
  exact ⟨X.map E.val, fun g => ⟨fun i j hij => by rw [e, (hX g).1 i j hij, map_zero],
    fun hg i => by rw [e, (hX g).2 hg i, map_zero]⟩⟩

private theorem cont_cyc (l : ℕ) [Fact l.Prime] : Continuous (cycA l l (PadicAlgCl l)) := by
  have hc : Continuous (cyc l l) := cyclotomicCharacter.continuous l ℚ_[l] (PadicAlgCl l)
  have ha : Continuous (algebraMap ℤ_[l] (PadicAlgCl l)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map (algebraMap ℤ_[l] (PadicAlgCl l) : ℤ_[l] →* PadicAlgCl l) ha).comp hc

private theorem small {K ι : Type} [TotallyDisconnectedSpace G] [Field K] [TopologicalSpace K] [T1Space K] [Finite ι]
    (f : ι → G → K) (hf : ∀ i, Continuous (f i)) (h1 : ∀ i, f i 1 = 1) {k : ℕ} (hk : 0 < k) :
    ∃ U : OpenNormalSubgroup G, ∀ i, ∀ g ∈ U, f i g ^ k = 1 → f i g = 1 := by
  have hfin : ({z : K | z ^ k = 1} \ {1}).Finite :=
    (Multiset.finite_toSet (Polynomial.nthRoots k (1 : K))).subset fun z hz => (Polynomial.mem_nthRoots hk).2 hz.1
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_iInter_of_finite fun i => hfin.isClosed.isOpen_compl.preimage (hf i))
    (Set.mem_iInter.2 fun i h => h.2 (h1 i))
  refine ⟨U, fun i g hg e => ?_⟩
  by_contra hne
  exact Set.mem_iInter.1 (hU hg) i ⟨e, hne⟩

end Bar

end UpperTheory.V.Th.OrdinaryBlock

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th

open UpperTheory.V.Th.OrdinaryBlock in
theorem UpperTheory.V.Th.bkOrd :
    Loc.LocalPublishedTheorems → BkOrd := by
  intro P l _ H _ _ _ _ _ φ hφ n ρ ψ m k hρ ⟨a, ha⟩ hm hk hI ⟨g₀, hg₀, hfree⟩ y hy
  rcases n with _ | n
  · exact ⟨1, 0, fun g => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun _ i => i.elim0⟩⟩
  have hρc : Continuous fun g => (a * ρ g * a⁻¹).val :=
    Units.continuous_val.comp ((continuous_const.mul hρ).mul continuous_const)
  have hψ : ∀ i, Continuous fun g => (ψ i g : Qbar l) := fun i => (hρc.matrix_elem i i).congr fun g => (ha g).2 i
  have hψ0 : Continuous fun g => (ψ 0 g⁻¹ : Qbar l) := (hψ 0).comp continuous_inv
  let r : H →* GL (Fin (n + 1)) (Qbar l) := MonoidHom.toHomUnits
    { toFun := fun g => (ψ 0 g⁻¹ : Qbar l) •
        (a * ρ g * a⁻¹).val
      map_one' := by simp
      map_mul' := fun g h => by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Units.val_mul, ← Units.val_mul, mul_inv_rev, map_mul, map_mul,
          mul_comm (ψ 0 h⁻¹)]
        congr 2
        group }
  have hr : ∀ g, (r g).val = (ψ 0 g⁻¹ : Qbar l) •
      (a * ρ g * a⁻¹).val := fun g => rfl
  have had : ∀ g (X : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l)),
      a.val * Loc.adGL ρ g X * (a⁻¹).val = Loc.adGL r g (a.val * X * (a⁻¹).val) := fun g X => by
    change a.val * ((ρ g).val * X * ((ρ g)⁻¹).val) * (a⁻¹).val = (r g).val * (a.val * X * (a⁻¹).val) * ((r g)⁻¹).val
    rw [← map_inv r, hr, hr, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Units.val_mul, ← map_mul,
      inv_inv, inv_mul_cancel, map_one, Units.val_one, one_smul, map_inv]
    simp only [Units.val_mul, Matrix.mul_assoc, Units.inv_mul_cancel_left]
  let f : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l) →ₗ[ℚ_[l]] Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l) :=
    { toFun := fun X => a.val * X * (a⁻¹).val
      map_add' := fun X Y => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  have hy' := Loc.z1fCoef φ (Loc.adGL ρ) (Loc.adGL r) f
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const) had y hy
  obtain ⟨U, hU⟩ := small
    (fun i g => ((ψ i g / ψ 0 g * Loc.cycA l l (Qbar l) (φ g) ^ (m 0 - m i) : (Qbar l)ˣ) : Qbar l))
    (fun i => by
      simp only [div_eq_mul_inv, ← map_inv, Units.val_mul]
      exact ((hψ i).mul hψ0).mul (Units.continuous_val.comp (((cont_cyc l).comp hφ.continuous).zpow _)))
    (fun i => by simp only [map_one, one_zpow, div_one, mul_one, Units.val_one]) hk
  haveI : Finite (H ⧸ U.toSubgroup) := U.toSubgroup.quotient_finite_of_isOpen U.isOpen
  haveI : U.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨X, hX⟩ := bar (κ := fun i => ψ i * (ψ 0)⁻¹) P hφ (r := r) (hψ0.smul hρc)
    (fun g => ⟨fun i j hij => by rw [hr, Matrix.smul_apply, (ha g).1 i j hij, smul_zero],
      fun i => by
        rw [hr, Matrix.smul_apply, (ha g).2 i, smul_eq_mul, mul_comm, map_inv]
        rfl⟩)
    (fun i => m i - m 0) (fun i j hij => sub_lt_sub_right (hm hij) _) U.toSubgroup U.isOpen
    (fun i g hg hg' => by
      have h1 := hU i g hg (by rw [← Units.val_pow_eq_pow_val, hI i 0 g hg', Units.val_one])
      rw [Units.val_eq_one, ← neg_sub, zpow_neg, mul_inv_eq_one, div_eq_mul_inv] at h1
      exact h1)
    (fun i j hij => ⟨g₀ ^ U.toSubgroup.index, U.toSubgroup.pow_index_mem g₀, fun e =>
      hfree i j hij.ne U.toSubgroup.index (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero) (by
        rw [map_pow φ, map_pow, map_pow, map_pow, hg₀, one_pow, Units.val_one, mul_one, Units.val_inj,
          MonoidHom.mul_apply, MonoidHom.mul_apply, mul_pow, mul_pow] at e
        exact mul_right_cancel e)⟩) _ hy'
  refine ⟨a, (a⁻¹).val * X * a.val, fun g => ?_⟩
  have e : a.val * (y g - (Loc.adGL ρ g ((a⁻¹).val * X * a.val) - (a⁻¹).val * X * a.val)) * (a⁻¹).val =
      f (y g) - (Loc.adGL r g X - X) := by
    have e0 : a.val * ((a⁻¹).val * X * a.val) * (a⁻¹).val = X := by
      simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, Matrix.mul_one]
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, had, e0]
    rfl
  rw [e]
  exact ⟨(ha g).1, (ha g).2, (hX g).1, (hX g).2⟩
