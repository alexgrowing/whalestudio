import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HasWeightAtOfTensorDualIntertwiner
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InjectiveInfinitePlaceOfEmbAtSplitPlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemMaximalCompactOfUnderEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsUnramifiedAtTotallyRealOfInertiaLeRestrictionR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLevelFixedVectorsDefiniteUnitaryEqProdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIntegralFixedVectorsEqOneAlmostAll
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Z.Mult (Cp)
open UpperTheory.V.Z.J.D
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section Alg

variable {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

private theorem rank_le_of (f : W' →ₗ[ℂ] W) (hf : Function.Injective f) (Z : Submodule ℂ W) (h : ∀ z, f z ∈ Z) :
    Module.rank ℂ W' ≤ Module.rank ℂ Z :=
  LinearMap.rank_le_of_injective (f.codRestrict Z h) fun _ _ e => hf (congrArg Subtype.val e)

private theorem box_tmul (ρ : Representation ℂ G W) (τ : Representation ℂ H W') (g : G × H) (x : W) (y : W') :
    box ρ τ g (x ⊗ₜ y) = ρ g.1 x ⊗ₜ τ g.2 y := rfl

private theorem box_fix (ρ : Representation ℂ G W) (τ : Representation ℂ H W') (K : Subgroup G) (K' : Subgroup H) :
    Module.rank ℂ (fixd ρ K) * Module.rank ℂ (fixd τ K') ≤ Module.rank ℂ (fixd (box ρ τ) (K.prod K')) := by
  rw [← rank_tensorProduct']
  have hi : Function.Injective (TensorProduct.map (fixd ρ K).subtype (fixd τ K').subtype) :=
    TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective Subtype.val_injective
  refine rank_le_of _ hi _ fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | tmul a b =>
    intro u hu
    rw [TensorProduct.map_tmul, box_tmul]
    exact congrArg₂ _ (a.2 _ hu.1) (b.2 _ hu.2)

private theorem pi_fix {I : Type} [Fintype I] {Gi Wi : I → Type} [∀ i, Group (Gi i)] [∀ i, AddCommGroup (Wi i)]
    [∀ i, Module ℂ (Wi i)] (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) (K : ∀ i, Subgroup (Gi i))
    (h : ∀ i, 0 < Module.finrank ℂ (fixd (τ i) (K i))) :
    ((∏ i, Module.finrank ℂ (fixd (τ i) (K i)) : ℕ) : Cardinal) ≤ Module.rank ℂ (fixd (piRep τ) (Subgroup.pi Set.univ K)) := by
  classical
  haveI : ∀ i, Module.Finite ℂ (fixd (τ i) (K i)) := fun i => Module.finite_of_finrank_pos (h i)
  have e : ((∏ i, Module.finrank ℂ (fixd (τ i) (K i)) : ℕ) : Cardinal) = Module.rank ℂ (⨂[ℂ] i, fixd (τ i) (K i)) := by
    rw [rank_eq_card_basis (Basis.piTensorProduct fun i => Module.finBasis ℂ (fixd (τ i) (K i)))]
    simp
  rw [e]
  choose r hr using fun i => (fixd (τ i) (K i)).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  have hi : Function.Injective (PiTensorProduct.map fun i => (fixd (τ i) (K i)).subtype) := by
    refine Function.LeftInverse.injective (g := PiTensorProduct.map r) fun z => ?_
    rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    simp only [hr, PiTensorProduct.map_id, LinearMap.id_apply]
  refine rank_le_of _ hi _ fun z => ?_
  induction z using PiTensorProduct.induction_on with
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | smul_tprod a f =>
    rw [map_smul]
    refine Submodule.smul_mem _ _ fun u hu => ?_
    rw [PiTensorProduct.map_tprod]
    refine (PiTensorProduct.map_tprod (fun i => τ i (u i)) _).trans ?_
    exact congrArg _ (funext fun i => (f i).2 _ (hu i trivial))

private theorem one_copy (hS : Step) (π : Representation ℂ G W) (τ : Representation ℂ G W') (Z : Submodule ℂ W)
    (ρ : Representation ℂ G Z) (hτ : AbsIrr τ) (hρ : Intw ρ π Z.subtype) (hI : Isot ρ τ) (hZ : Z ≠ ⊥) (K : Subgroup G)
    (P : ℕ) (hP : 0 < P) (h1 : (P : Cardinal) ≤ Module.rank ℂ (fixd τ K)) (h2 : Module.rank ℂ ↥(Z ⊓ fixd π K) ≤ P) :
    ∃ f : W' →ₗ[ℂ] W, Function.Injective f ∧ LinearMap.range f = Z ∧ Intw τ π f := by
  obtain ⟨X, _, _, κ, f, hf⟩ := hS G Unit Z W' (ρ.comp (MonoidHom.fst G Unit)) τ hτ hI
  have key : ∀ g m (x : X), (f (τ g m ⊗ₜ x) : W) = π g (f (m ⊗ₜ x)) := fun g m x => by
    have h := hf (g, 1) (m ⊗ₜ x)
    rw [box_tmul, map_one] at h
    exact (congrArg Subtype.val h).trans (hρ g _)
  have h3 : Module.rank ℂ (fixd τ K) * Module.rank ℂ X ≤ Module.rank ℂ ↥(Z ⊓ fixd π K) := by
    rw [← rank_tensorProduct']
    have hi : Function.Injective (Z.subtype ∘ₗ f.toLinearMap ∘ₗ LinearMap.rTensor X (fixd τ K).subtype) :=
      Subtype.val_injective.comp (f.injective.comp
        (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective))
    refine rank_le_of _ hi _ fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | tmul a b =>
      refine ⟨(f _).2, fun u hu => ?_⟩
      exact (key u a b).symm.trans (congrArg (fun m => (f (m ⊗ₜ b) : W)) (a.2 u hu))
  have h4 : Module.rank ℂ X ≤ 1 := by
    have h5 : (P : Cardinal) * Module.rank ℂ X ≤ P := (mul_le_mul_left h1 _).trans (h3.trans h2)
    by_contra hc
    have h6 : (2 : Cardinal) ≤ Module.rank ℂ X := by
      rw [← one_add_one_eq_two]
      exact Cardinal.add_one_le_of_lt (not_le.1 hc)
    have h7 : (P : Cardinal) * 2 ≤ P := (mul_le_mul_right h6 _).trans h5
    norm_cast at h7
    omega
  have h8 : Nontrivial X := by
    by_contra hc
    haveI := not_nontrivial_iff_subsingleton.1 hc
    haveI : Subsingleton Z := f.symm.injective.subsingleton
    exact hZ (Submodule.eq_bot_of_subsingleton)
  have h9 : Module.rank ℂ ℂ = Module.rank ℂ X := by
    rw [Module.rank_self]
    exact le_antisymm (Cardinal.one_le_iff_pos.2 rank_pos) h4
  obtain ⟨e⟩ := nonempty_linearEquiv_of_rank_eq h9
  let E : W' ≃ₗ[ℂ] Z := (TensorProduct.rid ℂ W').symm ≪≫ₗ LinearEquiv.lTensor W' e ≪≫ₗ f
  refine ⟨Z.subtype ∘ₗ E.toLinearMap, Subtype.val_injective.comp E.injective, ?_, fun g m => key g m (e 1)⟩
  rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]

end Alg

section Loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

open GlobalTheory.BCT (UL KL IsCompU)
open GlobalTheory.PRep (fixed)

private theorem loc_adm (hU : GlobalTheory.BCT.Unr E) (hn : 1 ≤ n) {σ : Submodule ℂ (UA E n → ℂ)} (hσ : IsAutRepU σ) (w : Plc E)
    (τ : SmIrr (UL n w)) (hτ : IsCompU σ w τ) (K : Subgroup (UL n w)) (hK : IsOpen (K : Set (UL n w))) :
    FiniteDimensional ℂ (fixed τ.ρ K) := by
  obtain ⟨⟨τ₀, h₀, hfd⟩, hu⟩ := GlobalTheory.BCT.LocCompU.exists_unique_locComp E hU n hn σ hσ w
  obtain ⟨T⟩ := hu τ₀ τ h₀ hτ
  haveI := hfd K hK
  exact GlobalTheory.BCT.SphLine.finiteDimensional_fixed_of_equiv T K

private theorem loc_one (hU : GlobalTheory.BCT.Unr E) (hn : 1 ≤ n) {σ : Submodule ℂ (UA E n → ℂ)} (hσ : IsAutRepU σ) (w : Plc E)
    (τ : SmIrr (UL n w)) (hτ : IsCompU σ w τ) (h : IsUnramU σ w) : Module.finrank ℂ (fixed τ.ρ (KL n w)) = 1 := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (GlobalTheory.T.unramifiedVector_gives_localComponent_sphericalVector E hU n σ hσ w τ hτ h)
  obtain ⟨θ, h1, h2, h3⟩ := GlobalTheory.BCT.SphLine.exists_gelfand_anti E hU n w
  obtain ⟨hKo, hKc⟩ := GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w
  rw [GlobalTheory.fixed_eq_span_of_gelfandPair (UL n w) (KL n w) hKo hKc θ h1 h2 h3 τ.V τ.ρ τ.irred
    ⟨τ.smooth, fun K hK _ => loc_adm hU hn hσ w τ hτ K hK⟩ x hx hx0, finrank_span_singleton hx0]

private theorem loc_deep (hU : GlobalTheory.BCT.Unr E) (hn : 1 ≤ n) {σ : Submodule ℂ (UA E n → ℂ)} (hσ : IsAutRepU σ) (w : Plc E)
    (τ : SmIrr (UL n w)) (hτ : IsCompU σ w τ) :
    ∃ K : Subgroup (UL n w), IsOpen (K : Set (UL n w)) ∧ K ≤ KL n w ∧ 0 < Module.finrank ℂ (fixed τ.ρ K) := by
  obtain ⟨h0, -⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 τ.irred
  obtain ⟨x, hx⟩ := exists_ne (0 : τ.V)
  let St : Subgroup (UL n w) :=
    { carrier := {k | τ.ρ k x = x}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have ho : IsOpen ((St ⊓ KL n w : Subgroup (UL n w)) : Set (UL n w)) :=
    (τ.smooth x).inter (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).1
  refine ⟨_, ho, inf_le_right, ?_⟩
  haveI := loc_adm hU hn hσ w τ hτ _ ho
  refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x, ?_⟩, fun h => hx (congrArg Subtype.val h)⟩
  rw [GlobalTheory.GelfandLine.mem_fixed_iff]
  exact fun k hk => hk.1

private theorem loc_move (hU : GlobalTheory.BCT.Unr E) (hn : 1 ≤ n) {σ : Submodule ℂ (UA E n → ℂ)} (hσ : IsAutRepU σ) {w : Plc E}
    (hw : IsSplitAt w) (τ : SmIrr (UL n w)) (hτ : IsCompU σ w τ) (τ' : SmIrr (GLw n w)) (h' : Cp σ w τ')
    (K : Subgroup (UL n w)) :
    Module.finrank ℂ (fixd τ'.ρ (K.map (UL n w).subtype)) = Module.finrank ℂ (fixed τ.ρ K) := by
  have hm : ∀ g : GLw n w, g ∈ UL n w := fun g => by
    rw [UL, if_pos hw]
    trivial
  let τ₁ : SmIrr (UL n w) :=
    { V := τ'.V
      ρ := τ'.ρ.comp (UL n w).subtype
      smooth := fun v => (τ'.smooth v).preimage continuous_subtype_val
      irred := by
        obtain ⟨h0, h⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 τ'.irred
        exact (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g x hx => hW ⟨g, hm g⟩ x hx⟩ }
  have h₁ : IsCompU σ w τ₁ := by
    obtain ⟨-, F, hF0, hFσ, hF⟩ := h'
    exact ⟨((cLoc w).comp (locU n w).subtype).codRestrict _ fun x => hm _, fun _ => rfl, τ₁.irred, F, hF0, hFσ,
      fun x v => hF x v⟩
  obtain ⟨T⟩ := (GlobalTheory.BCT.LocCompU.exists_unique_locComp E hU n hn σ hσ w).2 τ₁ τ h₁ hτ
  have hT : ∀ (k : UL n w) (x : τ'.V), T.toLinearEquiv (τ'.ρ k x) = τ.ρ k (T.toLinearEquiv x) := fun k x =>
    LinearMap.congr_fun (T.isIntertwining' k) x
  refine (T.toLinearEquiv.ofSubmodules _ _ ?_).finrank_eq
  ext y
  rw [GlobalTheory.GelfandLine.mem_fixed_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩ k hk
    exact (hT k x).symm.trans (congrArg T.toLinearEquiv (hx k ⟨k, hk, rfl⟩))
  · intro hy
    obtain ⟨x, rfl⟩ := T.toLinearEquiv.surjective y
    refine ⟨x, ?_, rfl⟩
    rintro _ ⟨k, hk, rfl⟩
    exact T.toLinearEquiv.injective ((hT k x).trans (hy k hk))

private theorem glob_dim (hU : GlobalTheory.BCT.Unr E) (hn : 1 ≤ n) {σ : Submodule ℂ (UA E n → ℂ)} (hσ : IsAutRepU σ)
    (sw : Plc (Lp E) → Plc E) (hsw : ∀ v, (sw v).under (𝓞 (Lp E)) = v) (T : Finset (Plc (Lp E)))
    (hsp : ∀ v ∈ T, IsSplitAt (sw v)) (hun : ∀ w : Plc E, w.under (𝓞 (Lp E)) ∉ T → IsUnramU σ w)
    (lam : InfinitePlace E → DomWeight n) (hlam : ∀ v, HasWeightAt σ v.embedding (lam v)) :
    ∃ (K : ∀ w : Plc E, Subgroup (GLw n w)) (a : Plc (Lp E) → ℕ) (U : Subgroup (finU E n)),
      (∀ x ∈ U, ∀ v, cLoc (sw v) x.1 ∈ K (sw v)) ∧ (∀ w, K w ≤ KO (w.adicCompletion E) (Fin n)) ∧
      (∀ v ∈ T, ∀ τ, Cp σ (sw v) τ → Module.finrank ℂ (fixd τ.ρ (K (sw v))) = a v) ∧ (∀ v, 0 < a v) ∧
      (Module.finrank ℂ ↥(σ ⊓ fixed (GlobalTheory.BCT.RF E n) U) : ℂ) = GlobalTheory.BCT.dimW lam * (∏ v ∈ T, a v : ℕ) := by
  choose τ hτ _ using fun w => (GlobalTheory.BCT.LocCompU.exists_unique_locComp E hU n hn σ hσ w).1
  have hex : ∀ w : Plc E, ∃ K : Subgroup (UL n w), IsOpen (K : Set (UL n w)) ∧ K ≤ KL n w ∧
      0 < Module.finrank ℂ (fixed (τ w).ρ K) ∧ (w.under (𝓞 (Lp E)) ∉ T → K = KL n w) := fun w => by
    by_cases h : w.under (𝓞 (Lp E)) ∈ T
    · obtain ⟨K, h1, h2, h3⟩ := loc_deep hU hn hσ w (τ w) (hτ w)
      exact ⟨K, h1, h2, h3, fun h' => absurd h h'⟩
    · refine ⟨KL n w, (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).1, le_rfl, ?_, fun _ => rfl⟩
      rw [loc_one hU hn hσ w (τ w) (hτ w) (hun w h)]
      exact one_pos
  choose K h1 h2 h3 h4 using hex
  have hinj : Function.Injective sw := Function.LeftInverse.injective hsw
  have hS : GlobalTheory.BCT.IsSection (Set.range sw) := fun w => ⟨sw (w.under (𝓞 (Lp E))), ⟨⟨_, rfl⟩, hsw _⟩, by
    rintro _ ⟨⟨v, rfl⟩, hv⟩
    rw [← hv, hsw]⟩
  have hfin : {w : Plc E | w.under (𝓞 (Lp E)) ∈ T}.Finite := by
    refine (T.finite_toSet.biUnion (t := fun v => {w : Plc E | w.under (𝓞 (Lp E)) = v}) fun v _ => ?_).subset
      fun w hw => Set.mem_biUnion hw rfl
    haveI := v.isMaximal
    refine Set.Finite.of_finite_image (f := fun w : Plc E => w.asIdeal)
      ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).subset ?_) fun _ _ _ _ h => HeightOneSpectrum.ext h
    rintro _ ⟨w, rfl, rfl⟩
    exact ⟨w.isPrime, ⟨rfl⟩⟩
  have hK : GlobalTheory.BCT.IsLevelFam (fun w : Plc E => MonoidHom.id (UL n w)) (KL n) K :=
    ⟨fun w => ⟨h1 w, h2 w, fun _ h => h⟩, hfin.subset fun w hw => by_contra fun h => hw (h4 w h)⟩
  refine ⟨fun w => (K w).map (UL n w).subtype, fun v => Module.finrank ℂ (fixed (τ (sw v)).ρ (K (sw v))),
    GlobalTheory.BCT.globLev (Set.range sw) K, fun x hx v => ?_, fun w => ?_,
    fun v hv τ' h' => loc_move hU hn hσ (hsp v hv) _ (hτ _) τ' h' _, fun v => h3 _, ?_⟩
  · exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx (sw v)) ⟨v, rfl⟩
  · rintro _ ⟨k, hk, rfl⟩
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact h2 w hk
  · rw [GlobalTheory.T.finrank_levelFixedVectors_definiteUnitary_eq_prod E hU n hn σ hσ _ hS lam hlam K hK τ hτ, finprod_mem_range hinj, Nat.cast_prod]
    congr 1
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => by_contra fun h => hv ?_
    have h' : (sw v).under (𝓞 (Lp E)) ∉ T := by rwa [hsw]
    beta_reduce
    rw [h4 _ h', loc_one hU hn hσ _ (τ _) (hτ _) (hun _ h'), Nat.cast_one]

end Loc

section Glob

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] {n : ℕ}

private theorem cmp_of {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) :
    cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dif_pos h]
  rfl

private theorem l_under {u : Plc L} :
    ((l : ℕ) : 𝓞 L) ∈ u.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ (u.under (𝓞 (Lp L))).asIdeal := by
  change _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ u.asIdeal
  rw [map_natCast]

private theorem cLoc_inf {x : UA L n} (h : x ∈ infU L n) (u : Plc L) : cLoc u x = 1 := by
  have h1 : Matrix.GeneralLinearGroup.map (pFin L) x.1 = 1 := h
  have e : cLoc u x = Matrix.GeneralLinearGroup.map (pLoc L u) (Matrix.GeneralLinearGroup.map (pFin L) x.1) := Units.ext rfl
  rw [e, h1, map_one]

variable (s : HidaSetting l L Ω)

private theorem under_w (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem SectionSplitPlaces : ((l : ℕ) : 𝓞 (Lp L)) ∉ s.v0.asIdeal := by
  intro h
  have hcard : Nat.card (𝓞 (Lp L) ⧸ s.v0.asIdeal) = s.p := s.norm_v0_eq_one
  have hl0 : ((l : ℕ) : 𝓞 (Lp L) ⧸ s.v0.asIdeal) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem.2 h)
  have hp0 : ((s.p : ℕ) : 𝓞 (Lp L) ⧸ s.v0.asIdeal) = 0 := by
    have := card_nsmul_eq_zero' (G := 𝓞 (Lp L) ⧸ s.v0.asIdeal) (x := 1)
    rw [hcard] at this
    simpa using this
  obtain ⟨a, b, e⟩ := ((Nat.coprime_primes (Fact.out : l.Prime) s.p_prime).2 (Ne.symm s.p_ne)).isCoprime
  have e' := congrArg (Int.cast : ℤ → 𝓞 (Lp L) ⧸ s.v0.asIdeal) e
  push_cast at e'
  rw [hl0, hp0, mul_zero, mul_zero, add_zero] at e'
  haveI := subsingleton_of_zero_eq_one e'
  rw [Nat.card_of_subsingleton (0 : 𝓞 (Lp L) ⧸ s.v0.asIdeal)] at hcard
  exact s.p_prime.one_lt.ne hcard

private theorem cmp_S {v : Plc (Lp L)} (h : v ∈ s.St ∨ v = s.v0) (x : UA L n) :
    cmp n (s.w v) ((away l L n).rangeRestrict x) = cLoc (s.w v) x := by
  refine cmp_of (fun e => ?_) x
  have e' := l_under.1 e
  rw [under_w] at e'
  rcases h with h | rfl
  · exact s.St_l _ h e'
  · exact SectionSplitPlaces s e'

private theorem cmp_off {w : Plc L} (h : w.under (𝓞 (Lp L)) ∉ s.S) (x : UA L n) :
    cmp n w ((away l L n).rangeRestrict x) = cLoc w x := cmp_of (fun e => h (Or.inl (l_under.1 e))) x

private theorem mem_KS {a : Ga l L n} (h1 : toGS n s a = 1)
    (h2 : ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.S → cmp n w a ∈ KO (w.adicCompletion L) (Fin n)) : a ∈ KS n s :=
  Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => h2 w hw⟩

private theorem sec_spec (hb : Function.Bijective ((toGS n s).comp (GaS n s).subtype)) (g : GS n s) :
    toGS n s (secS n s g) = g ∧ ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.S → cmp n w (secS n s g) = 1 := by
  unfold secS
  rw [dif_pos hb]
  refine ⟨(MulEquiv.ofBijective _ hb).apply_symm_apply g, fun w hw => ?_⟩
  exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ((MulEquiv.ofBijective _ hb).symm g).2 w)
    ⟨fun h => hw (Or.inr (Or.inl h)), fun h => hw (Or.inr (Or.inr h))⟩

private theorem sec_rest (hb : Function.Bijective ((toGS n s).comp (GaS n s).subtype)) (x : UA L n)
    (hx : ∀ v, cLoc (s.w v) x ∈ KO ((s.w v).adicCompletion L) (Fin n)) :
    (secS n s (toGS n s ((away l L n).rangeRestrict x)))⁻¹ * (away l L n).rangeRestrict x ∈ KS n s := by
  refine mem_KS s ?_ fun w hw => ?_
  · rw [map_mul, map_inv, (sec_spec s hb _).1, inv_mul_cancel]
  · rw [map_mul, map_inv, (sec_spec s hb _).2 w hw, inv_one, one_mul, cmp_off s hw]
    exact UpperTheory.mem_maximalCompact_of_under_eq L n x _ w (under_w s _).symm (hx _)

private theorem prod_S [Fintype (Vl l L)] : ∃ T : Finset (Plc (Lp L)), (∀ v, v ∈ T ↔ v ∈ s.S) ∧
    ∀ a : Plc (Lp L) → ℕ, ∏ v ∈ T, a v = (∏ v : Vl l L, a v.1) * ((∏ u : s.St, a u) * a s.v0) := by
  classical
  refine ⟨(Finset.univ : Finset (Vl l L)).map (Function.Embedding.subtype _) ∪ insert s.v0 s.St, fun v => ?_, fun a => ?_⟩
  · simp only [Finset.mem_union, Finset.mem_map, Finset.mem_insert, Finset.mem_univ, true_and]
    exact or_congr ⟨fun ⟨u, hu⟩ => hu ▸ u.2, fun h => ⟨⟨v, h⟩, rfl⟩⟩ or_comm
  · rw [Finset.prod_union, Finset.prod_map, Finset.prod_insert s.v0_St, Finset.prod_coe_sort s.St a, mul_comm (a s.v0)]
    · rfl
    · refine Finset.disjoint_left.2 fun v hv hv' => ?_
      obtain ⟨u, -, rfl⟩ := Finset.mem_map.1 hv
      rcases Finset.mem_insert.1 hv' with h | h
      · exact SectionSplitPlaces s (h ▸ u.2)
      · exact s.St_l _ h u.2

variable {s} (V : s.Lev)

private theorem fix_J {d : ℕ} (hb : Function.Bijective ((toGS n s).comp (GaS n s).subtype))
    (K : ∀ w : Plc L, Subgroup (GLw n w)) (hK : ∀ w, K w ≤ KO (w.adicCompletion L) (Fin n))
    (F : Ga l L n × GL' n V → Fin d → ℂ)
    (h1 : F ∈ fixd ((rtr ℂ (Ga l L n × GL' n V) (Fin d → ℂ)).comp (MonoidHom.inl _ _)) (KS n s))
    (h2 : F ∈ fixd (actS n V d) ((Subgroup.pi Set.univ fun v : V.frame.Vl => K (s.w v.1)).prod
      ((Subgroup.pi Set.univ fun u : s.St => K (s.w u)).prod (K (s.w s.v0)))))
    (x : UA L n) (hx : ∀ v, cLoc (s.w v) x ∈ K (s.w v)) :
    rtr ℂ (Ga l L n × GL' n V) (Fin d → ℂ) ((away l L n).rangeRestrict x, fun v : V.frame.Vl => cLoc (s.w v.1) x) F = F := by
  have e1 := h1 _ (sec_rest s hb x fun v => hK _ (hx v))
  have e2 := h2 (fun v : V.frame.Vl => cLoc (s.w v.1) x, toGS n s ((away l L n).rangeRestrict x))
    ⟨fun v _ => hx v.1, fun u _ => Set.mem_of_eq_of_mem (cmp_S s (Or.inl u.2) x) (hx u.1),
      Set.mem_of_eq_of_mem (cmp_S s (Or.inr rfl) x) (hx _)⟩
  funext y
  refine Eq.trans ?_ (congrFun e2 y)
  refine Eq.trans (congrArg F ?_)
    (congrFun e1 (y * (secS n s (toGS n s ((away l L n).rangeRestrict x)), fun v : V.frame.Vl => cLoc (s.w v.1) x)))
  refine Prod.ext ?_ (mul_one _).symm
  exact congrArg (y.1 * ·) (mul_inv_cancel_left _ _).symm |>.trans (mul_assoc _ _ _).symm

variable {V} (ι : Qbar l ≃+* ℂ) {lam : Wt L l n} {d : ℕ}
  (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))

private theorem span_form (σ : Submodule ℂ (UA L n → ℂ)) (F : Ga l L n × GL' n V → Fin d → ℂ)
    (h : F ∈ Submodule.span ℂ {F : Ga l L n × GL' n V → Fin d → ℂ | ∀ ℓ, toForm ι e F ℓ ∈ σ}) : ∀ ℓ, toForm ι e F ℓ ∈ σ := by
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    intro ℓ
    have : toForm ι e (0 : Ga l L n × GL' n V → Fin d → ℂ) ℓ = 0 := by
      funext g
      simp only [toForm, Pi.zero_apply, map_zero]
    rw [this]; exact σ.zero_mem
  | add x y _ _ hx hy =>
    intro ℓ
    have : toForm ι e (x + y) ℓ = toForm ι e x ℓ + toForm ι e y ℓ := by
      funext g
      simp only [toForm, Pi.add_apply, map_add]
    rw [this]; exact σ.add_mem (hx ℓ) (hy ℓ)
  | smul a x _ hx =>
    intro ℓ
    have : toForm ι e (a • x) ℓ = a • toForm ι e x ℓ := by
      funext g
      simp only [toForm, Pi.smul_apply, map_smul]
    rw [this]; exact σ.smul_mem a (hx ℓ)

private theorem infRep_fin {k : UA L n} (hk : k ∈ finU L n) : infRep (V := V) ι lam k = 1 := by
  have h1 : ∀ τ : L →+* ℂ, cEmb τ k = 1 := fun τ => by
    change Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1
    rw [MonoidHom.mem_ker.1 hk, map_one]
  change PiTensorProduct.mapMonoidHom (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) =>
    GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb (ι.toRingHom.comp y.res) k)) = 1
  simp only [h1, map_one]
  exact map_one _

private theorem form_wt (hn : 1 ≤ n)
    (h3 : ∀ (F : Ga l L n × GL' n V → Fin d → ℂ) ℓ (x : UA L n), RU L n x (toForm ι e F ℓ) =
      toForm ι e (fun g => F (g * ((away l L n).rangeRestrict x, fun v : V.frame.Vl => cLoc (s.w v.1) x))) (ℓ ∘ₗ infRep ι lam x⁻¹))
    (σ : Submodule ℂ (UA L n → ℂ)) (F : Ga l L n × GL' n V → Fin d → ℂ) (hF : ¬ ∀ ℓ, toForm ι e F ℓ = 0)
    (hσ : ∀ ℓ, toForm ι e F ℓ ∈ σ) (y : Emb l (fun v : V.frame.Vl => s.w v.1)) :
    HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual := by
  haveI : Finite V.frame.Vl := @Finite.of_fintype _ V.frame.finV
  haveI : ∀ v : V.frame.Vl, Finite (W.Emb l (s.w v.1)) := fun v => GlobalTheory.HeckeGal.finite_contEmb _
  let Φ : Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ) :=
    { toFun := fun ℓ => toForm ι e F ℓ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine UpperTheory.hasWeightAt_of_tensor_dual_intertwiner L n hn _ (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) => ι.toRingHom.comp y.res)
    (UpperTheory.injective_infinitePlace_of_emb_at_split_places l L Ω s V ι) (fun y => lam y.res) σ Φ (fun h0 => hF fun ℓ => LinearMap.congr_fun h0 ℓ) hσ
    (fun ℓ x hx => ?_) y
  have h1 : (((away l L n).rangeRestrict x, fun v : V.frame.Vl => cLoc (s.w v.1) x) : Ga l L n × GL' n V) = 1 :=
    Prod.ext (Subtype.ext (funext fun u => cLoc_inf hx u.1)) (funext fun v => cLoc_inf hx _)
  have h2 := h3 F ℓ x
  simp only [h1, mul_one] at h2
  exact h2

private theorem form_unr
    (h3 : ∀ (F : Ga l L n × GL' n V → Fin d → ℂ) ℓ (x : UA L n), RU L n x (toForm ι e F ℓ) =
      toForm ι e (fun g => F (g * ((away l L n).rangeRestrict x, fun v : V.frame.Vl => cLoc (s.w v.1) x))) (ℓ ∘ₗ infRep ι lam x⁻¹))
    (σ : Submodule ℂ (UA L n → ℂ)) (F : Ga l L n × GL' n V → Fin d → ℂ) (hF : ¬ ∀ ℓ, toForm ι e F ℓ = 0)
    (hσ : ∀ ℓ, toForm ι e F ℓ ∈ σ)
    (h1 : F ∈ fixd ((rtr ℂ (Ga l L n × GL' n V) (Fin d → ℂ)).comp (MonoidHom.inl _ _)) (KS n s))
    (w : Plc L) (hw : w.under (𝓞 (Lp L)) ∉ s.S) : IsUnramU σ w := by
  obtain ⟨ℓ, hℓ⟩ := not_forall.1 hF
  refine ⟨_, hσ ℓ, hℓ, fun x hx hk => ?_⟩
  have hS : ∀ v ∈ s.S, cLoc (s.w v) x = 1 := fun v hv =>
    GlobalTheory.DefU.LocRet.mem_locU_ne hx fun h => hw (h ▸ (under_w s v).symm ▸ hv)
  have hK : cLoc w x ∈ KO (w.adicCompletion L) (Fin n) := by
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact hk
  have hm : (away l L n).rangeRestrict x ∈ KS n s := by
    refine mem_KS s (Prod.ext (funext fun u => (cmp_S s (Or.inl u.2) x).trans (hS _ (Or.inr (Or.inl u.2))))
      ((cmp_S s (Or.inr rfl) x).trans (hS _ (Or.inr (Or.inr rfl))))) fun u hu => ?_
    rw [cmp_off s hu]
    by_cases h : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
    · exact UpperTheory.mem_maximalCompact_of_under_eq L n x w u h hK
    · rw [show cLoc u x = 1 from GlobalTheory.DefU.LocRet.mem_locU_ne hx h]
      exact one_mem _
  have hl : (fun v : V.frame.Vl => cLoc (s.w v.1) x) = 1 := funext fun v => hS v.1 (Or.inl v.2)
  rw [h3, hl, infRep_fin ι ((finU L n).inv_mem (Subgroup.mem_inf.1 hx).1)]
  exact congrArg (fun G => toForm ι e G ℓ) (h1 _ hm)

end Glob

section Model

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] {n : ℕ} {s : HidaSetting l L Ω} {V : s.Lev} {σ : Submodule ℂ (UA L n → ℂ)} (C : Comps V σ)

private theorem model_irr (hB : BoxIrr) (hP : PiIrr) (hG : SchurGL) : AbsIrr (box C.repL C.repS) := by
  classical
  letI : Fintype V.frame.Vl := V.frame.finV
  exact hB _ _ _ _ _ _ (hP _ _ _ _ fun v => hG L n _ _) (hB _ _ _ _ _ _ (hP _ _ _ _ fun u => hG L n _ _) (hG L n _ _))

private theorem model_rank [Fintype V.frame.Vl] (K : ∀ w : Plc L, Subgroup (GLw n w)) (a : Plc (Lp L) → ℕ) (k4 : ∀ v, 0 < a v)
    (k3 : ∀ v ∈ s.S, ∀ τ, Cp σ (s.w v) τ → Module.finrank ℂ (fixd τ.ρ (K (s.w v))) = a v) :
    (((∏ v : V.frame.Vl, a v.1) * ((∏ u : s.St, a u) * a s.v0) : ℕ) : Cardinal) ≤
      Module.rank ℂ (fixd (box C.repL C.repS) ((Subgroup.pi Set.univ fun v : V.frame.Vl => K (s.w v.1)).prod
        ((Subgroup.pi Set.univ fun u : s.St => K (s.w u)).prod (K (s.w s.v0))))) := by
  have el := fun v : V.frame.Vl => k3 v.1 (Or.inl v.2) _ (C.hl v)
  have eu := fun u : s.St => k3 u.1 (Or.inr (Or.inl u.2)) _ (C.hu u)
  have eo := k3 s.v0 (Or.inr (Or.inr rfl)) _ C.ho
  have rl := pi_fix (fun v => (C.l v).ρ) (fun v => K (s.w v.1)) fun v => (k4 _).trans_eq (el v).symm
  have ru := pi_fix (fun u => (C.u u).ρ) (fun u => K (s.w u.1)) fun u => (k4 _).trans_eq (eu u).symm
  have ro : (a s.v0 : Cardinal) ≤ Module.rank ℂ (fixd C.o.ρ (K (s.w s.v0))) := by
    haveI := Module.finite_of_finrank_pos ((k4 _).trans_eq eo.symm)
    exact ((congrArg Nat.cast eo).symm.trans (Module.finrank_eq_rank _ _)).le
  rw [Finset.prod_congr rfl fun v _ => el v] at rl
  rw [Finset.prod_congr rfl fun u _ => eu u] at ru
  rw [Nat.cast_mul, Nat.cast_mul]
  exact (mul_le_mul' rl ((mul_le_mul' ru ro).trans (box_fix _ _ _ _))).trans (box_fix _ _ _ _)

private theorem level_le (hb : Function.Bijective ((toGS n s).comp (GaS n s).subtype)) {d : ℕ}
    (K : ∀ w : Plc L, Subgroup (GLw n w)) (hK : ∀ w, K w ≤ KO (w.adicCompletion L) (Fin n)) (U : Subgroup (finU L n))
    (hU : ∀ x ∈ U, ∀ v, cLoc (s.w v) x.1 ∈ K (s.w v)) (B : Submodule ℂ (Ga l L n × GL' n V → Fin d → ℂ)) :
    (B ⊓ fixd ((rtr ℂ (Ga l L n × GL' n V) (Fin d → ℂ)).comp (MonoidHom.inl _ _)) (KS n s)) ⊓
      fixd (actS n V d) ((Subgroup.pi Set.univ fun v : V.frame.Vl => K (s.w v.1)).prod
        ((Subgroup.pi Set.univ fun u : s.St => K (s.w u)).prod (K (s.w s.v0)))) ≤
    B ⊓ fixd (rtr ℂ (Ga l L n × GL' n V) (Fin d → ℂ)) (U.map ((MonoidHom.prod (away l L n).rangeRestrict
      (Pi.monoidHom fun v : V.frame.Vl => cLoc (s.w v.1))).comp (finU L n).subtype)) := by
  refine fun G hG => ⟨hG.1.1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact fix_J V hb K hK G hG.1.2 hG.2 x.1 (hU x hx)

end Model

private theorem vs_data {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (hn : 1 ≤ n) {V : s.Lev} (Q : QData V) {c : Coef l} (ι : Qbar l ≃+* ℂ) {m : ℕ}
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O) {lam : Wt L l n} {d : ℕ}
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (hξ : IsBasis ι e ξ) (σ : Submodule ℂ (UA L n → ℂ))
    (hne : VS V ι e ξ Q τ₀ σ ≠ ⊥) :
    (∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual) ∧
      (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.S → IsUnramU σ w) ∧ d ≠ 0 := by
  have f := formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hF1 := mt (f.1 F hF.1.1) hF0
  have hF2 := span_form ι e σ F hF.1.2
  refine ⟨form_wt ι e hn f.2.2.1 σ F hF1 hF2, form_unr ι e f.2.2.1 σ F hF1 hF2 hF.2, fun h => hF0 (funext fun _ => funext fun i => ?_)⟩
  exact (h ▸ i : Fin 0).elim0

private theorem cancel_rank {r y : Cardinal} {f d P : ℕ} {D : ℂ} (hP : 0 < P) (hd : d ≠ 0) (h1 : r = y * d) (h2 : (d : ℂ) = D)
    (h3 : (f : ℂ) = D * (P : ℕ)) (h4 : 0 < f → r = f) : y ≤ P := by
  have h5 : f = P * d := by
    rw [← h2, mul_comm] at h3
    exact_mod_cast h3
  have h6 : y * d = (P : Cardinal) * d := by
    rw [← h1, h4 (h5 ▸ Nat.mul_pos hP (Nat.pos_of_ne_zero hd)), h5, Nat.cast_mul]
  exact ((Cardinal.mul_natCast_inj hd).1 h6).le

theorem UpperTheory.V.Z.J.D.flath :
    IsotS → Step → BoxIrr → PiIrr → SchurGL → InfDim → WtEx → SecS → Flath := by
  intro hI hS hB hP hG hD hW hSec l _ L Ω _ _ _ _ _ _ s n hn V hV Q c ι m τ₀ lam d e ξ hξ σ hσ hne C
  letI : Fintype V.frame.Vl := V.frame.finV
  refine (hI l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ hξ σ hσ C).elim fun ρ hρ => ?_
  obtain ⟨lam', hl⟩ := hW l L Ω s n hn V hV ι lam
  have hv := vs_data hn Q ι τ₀ e ξ hξ σ hne
  have hwt := (hl σ hσ).1 hv.1
  obtain ⟨T, hT, hprod⟩ := @prod_S l _ L Ω _ _ _ _ _ _ s V.frame.finV
  refine (glob_dim (UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr) hn hσ s.w (under_w s) T
    (fun v hv => UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA v) (s.split v ((hT v).1 hv)) _ (under_w s v))
    (fun w hw => hv.2.1 w fun h => hw ((hT _).2 h)) lam' hwt).elim fun K hK => hK.elim fun a ha => ha.elim fun U k => ?_
  have d1 := hD l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ hξ lam' hl σ hσ hwt U _ rfl
  have hPp : 0 < ∏ v ∈ T, a v := Finset.prod_pos fun v _ => k.2.2.2.1 v
  have hY := cancel_rank hPp hv.2.2 d1.1 d1.2 k.2.2.2.2 fun h =>
    haveI := Module.finite_of_finrank_pos h
    (Module.finrank_eq_rank _ _).symm
  have h1 := model_rank C K a k.2.2.2.1 fun v h => k.2.2.1 v ((hT v).2 h)
  exact one_copy hS (actS n V d) (box C.repL C.repS) _ ρ (model_irr C hB hP hG) hρ.1 hρ.2 hne _ _ hPp
    ((congrArg Nat.cast (hprod a)).trans_le h1)
    ((Submodule.rank_mono (level_le (hSec l L Ω s n hn V hV).1 K k.2.1 U k.1 _)).trans hY)
