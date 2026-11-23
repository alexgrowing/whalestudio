import Development.WeilBound.ThetaLifts.SmallCones.KFinArch

noncomputable section

namespace PositivityTheory.ThKCT.So

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open PositivityTheory.ThKOwn.KPol
open scoped TensorProduct Classical Matrix

theorem sb_unif {Y : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] {g : Y → ℂ} (hg : g ∈ SB Y) :
    ∀ᶠ u in 𝓝 (0 : Y), ∀ y, g (y + u) = g y := by
  have h1 : ∀ᶠ u in 𝓝 (0 : Y), ∀ y ∈ tsupport g, g (y + u) = g y := by
    refine hg.2.isCompact.eventually_forall_of_forall_eventually fun y _ => ?_
    have a : Tendsto (fun z : Y × Y => z.2 + z.1) (𝓝 (0, y)) (𝓝 y) := by
      exact (continuous_snd.add continuous_fst).tendsto' ((0 : Y), y) y (add_zero y)
    filter_upwards [a.eventually (hg.1.eventually_eq y), (continuous_snd.tendsto ((0 : Y), y)).eventually (hg.1.eventually_eq y)]
      with z h h'
    rw [h, h']
  have h2 : ∀ᶠ u in 𝓝 (0 : Y), ∀ y ∈ tsupport g, g (y + -u) = g y := by
    have : Tendsto (fun u : Y => -u) (𝓝 0) (𝓝 0) := by simpa using continuous_neg.tendsto (0 : Y)
    exact this.eventually h1
  filter_upwards [h1, h2] with u a b y
  by_cases hy : y ∈ tsupport g
  · exact a y hy
  by_cases hy' : y + u ∈ tsupport g
  · rw [← b _ hy', add_neg_cancel_right]
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hy']

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def Lev (C U : Set (κ → Af F)) (Ψ : (κ → AF F) → ℂ) : Prop :=
  (∀ x, ∀ y ∉ C, Ψ (pt x y) = 0) ∧ ∀ x y, ∀ u ∈ U, Ψ (pt x (y + u)) = Ψ (pt x y)

theorem exists_lev {Ψ} (h : Ψ ∈ schA F κ) : ∃ C, IsCompact C ∧ ∃ U ∈ 𝓝 0, Lev C U Ψ := by
  induction h using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact ⟨_, hg.2.isCompact, _, sb_unif hg, fun x y hy => by rw [pureA_pt, image_eq_zero_of_notMem_tsupport hy, mul_zero],
      fun x y u hu => by rw [pureA_pt, pureA_pt, hu y]⟩
  | zero => exact ⟨∅, isCompact_empty, _, univ_mem, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨C, hC, U, hU, a, b⟩ := h1
    obtain ⟨C', hC', U', hU', a', b'⟩ := h2
    exact ⟨_, hC.union hC', _, inter_mem hU hU', fun x y hy => by
      rw [Pi.add_apply, a x y fun h => hy (Or.inl h), a' x y fun h => hy (Or.inr h), add_zero],
      fun x y u hu => by rw [Pi.add_apply, Pi.add_apply, b x y u hu.1, b' x y u hu.2]⟩
  | smul c Φ _ h =>
    obtain ⟨C, hC, U, hU, a, b⟩ := h
    exact ⟨C, hC, U, hU, fun x y hy => by rw [Pi.smul_apply, a x y hy, smul_zero],
      fun x y u hu => by rw [Pi.smul_apply, Pi.smul_apply, b x y u hu]⟩

def slc (P : Submodule ℂ (SInf F κ)) : Submodule ℂ ((κ → AF F) → ℂ) where
  carrier := {Ψ | ∀ y, ∃ f ∈ P, ∀ x, Ψ (pt x y) = f x}
  zero_mem' := fun _ => ⟨0, zero_mem _, fun _ => rfl⟩
  add_mem' := fun ha hb y => by
    obtain ⟨f, hf, e⟩ := ha y
    obtain ⟨f', hf', e'⟩ := hb y
    exact ⟨f + f', add_mem hf hf', fun x => by rw [Pi.add_apply, e, e', SchwartzMap.add_apply]⟩
  smul_mem' := fun c _ ha y => by
    obtain ⟨f, hf, e⟩ := ha y
    exact ⟨c • f, Submodule.smul_mem _ c hf, fun x => by rw [Pi.smul_apply, e, SchwartzMap.smul_apply]⟩

theorem slc_mono {P Q : Submodule ℂ (SInf F κ)} (h : P ≤ Q) : slc P ≤ slc Q := fun _ hΨ y =>
  (hΨ y).imp fun _ hf => ⟨h hf.1, hf.2⟩

def levS (C U : Set (κ → Af F)) : Submodule ℂ ((κ → AF F) → ℂ) where
  carrier := {Ψ | Lev C U Ψ}
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  add_mem' := fun ha hb => ⟨fun x y hy => by rw [Pi.add_apply, ha.1 x y hy, hb.1 x y hy, add_zero],
    fun x y u hu => by rw [Pi.add_apply, Pi.add_apply, ha.2 x y u hu, hb.2 x y u hu]⟩
  smul_mem' := fun c _ ha => ⟨fun x y hy => by rw [Pi.smul_apply, ha.1 x y hy, smul_zero],
    fun x y u hu => by rw [Pi.smul_apply, Pi.smul_apply, ha.2 x y u hu]⟩

theorem orbit_fin {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (ρ : G →* Module.End ℂ ((κ → AF F) → ℂ)) (Φ : (κ → AF F) → ℂ) (hc : ∀ z, Continuous fun k => ρ k Φ z)
    (hs : ∀ k, ρ k Φ ∈ schA F κ) (P : Submodule ℂ (SInf F κ)) [FiniteDimensional ℂ P] (hP : ∀ k, ρ k Φ ∈ slc P) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => ρ k Φ)) := by
  haveI : LocallyCompactSpace (Af F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  let C := CompactExhaustion.choice (κ → Af F)
  obtain ⟨U, hU⟩ := (𝓝 (0 : κ → Af F)).exists_antitone_basis
  obtain ⟨⟨a, b⟩, k₀, hk₀⟩ := nonempty_interior_of_iUnion_of_closed (f := fun p : ℕ × ℕ => {k | Lev (C p.1) (U p.2) (ρ k Φ)})
    (fun p => by
      simp only [Lev, Set.setOf_and, Set.setOf_forall]
      exact (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ => isClosed_eq (hc _) continuous_const).inter
        (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_eq (hc _) (hc _)))
    (Set.eq_univ_of_forall fun k => by
      obtain ⟨D, hD, V, hV, h1, h2⟩ := exists_lev (hs k)
      obtain ⟨a, ha⟩ := C.exists_superset_of_isCompact hD
      obtain ⟨b, hb⟩ := hU.mem_iff.1 hV
      exact Set.mem_iUnion.2 ⟨(a, b), fun x y hy => h1 x y fun h => hy (ha h), fun x y u hu => h2 x y u (hb hu)⟩)
  let Ω := slc P ⊓ levS (C a) (U b)
  let c : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) :=
    { toFun := fun f => f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  haveI : FiniteDimensional ℂ Ω := level_fin pt (fun z => ⟨_, _, pt_eta z⟩) c P (C.isCompact a) (hU.mem b) Ω (fun Ψ h => h.1)
    (fun Ψ h => h.2.1) fun Ψ h => h.2.2
  obtain ⟨s, -, hcov⟩ := isCompact_univ.elim_nhds_subcover
    (fun k₁ : G => (fun k => k₀ * k₁⁻¹ * k) ⁻¹' {k | Lev (C a) (U b) (ρ k Φ)}) fun k₁ _ =>
      (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.1 hk₀)
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ k₁ : s, Ω.map (ρ (k₁.1 * k₀⁻¹))) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  obtain ⟨k₁, h₁, hk⟩ := Set.mem_iUnion₂.1 (hcov (Set.mem_univ k))
  refine Submodule.mem_iSup_of_mem ⟨k₁, h₁⟩ ⟨ρ (k₀ * k₁⁻¹ * k) Φ, ⟨hP _, hk⟩, ?_⟩
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

end PositivityTheory.ThKCT.So

namespace PositivityTheory.ThKCT

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open PositivityTheory.ThKOwn.KPol So
open scoped TensorProduct Classical Matrix

theorem kFinData_of (hS : StabEx) : KFinData := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP K hK Φ hΦ
  have hs := IsUWeilPair.isUSplitting hP.weil
  have h1 : Φ ∈ schA F (Fin n × Fin d) ∧ ∃ m, ∀ k ∈ K, om (k, 1) Φ ∈ slc (polM M B.emb m) := by
    induction hΦ using Submodule.span_induction with
    | mem Φ h =>
      obtain ⟨f, hf, φ, h1, h2, rfl⟩ := h
      obtain ⟨g, hg, e⟩ := GlobalTheory.CompanionTheory.Ar.RT.Inj.pure_eq_pureA M B.ψ hP.good φ h1 h2
      obtain ⟨m, hm⟩ := exists_polM M hP.base.std hf
      rw [e f]
      refine ⟨Submodule.subset_span ⟨f, g, hg, rfl⟩, m, fun k hk y => ?_⟩
      obtain ⟨A, hA⟩ := exists_slice hs.toIsSplitting (k, 1) hg y
      exact ⟨A f, polM_stab hP.base.std hs.toIsSplitting hg ((hK _).1 (inv_mem hk)).1 hA m hm, hA f⟩
    | zero => exact ⟨zero_mem _, 0, fun k _ => by rw [map_zero]; exact zero_mem _⟩
    | add a b _ _ ha hb =>
      obtain ⟨a1, m, hm⟩ := ha
      obtain ⟨b1, m', hm'⟩ := hb
      refine ⟨add_mem a1 b1, max m m', fun k hk => ?_⟩
      rw [map_add]
      exact add_mem (slc_mono (fil_mono _ _ (le_max_left _ _)) (hm k hk)) (slc_mono (fil_mono _ _ (le_max_right _ _)) (hm' k hk))
    | smul c a _ ha =>
      obtain ⟨a1, m, hm⟩ := ha
      refine ⟨Submodule.smul_mem _ c a1, m, fun k hk => ?_⟩
      rw [map_smul]
      exact Submodule.smul_mem _ c (hm k hk)
  obtain ⟨h1, m, hm⟩ := h1
  refine ⟨h1, ?_⟩
  obtain ⟨K', -, -, hK', hc, -⟩ := hS F E σ B n X r s hP.base hP.herm
  obtain rfl : K = K' := Subgroup.ext fun g => (hK g).trans (hK' g).symm
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc
  haveI := polM_fin M hP.base.cm B.emb m
  refine orbit_fin (om.comp ((MonoidHom.inl _ _).comp K.subtype)) Φ (fun z => ?_) (fun k => hs.pres _ _ h1) _ fun k => hm k.1 k.2
  let l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj z
  have hl' : l ∈ (adeleClass F).adm (Fin n × Fin d) := fun g' _ =>
    ⟨g' (fun i => (z i).2) • (BoundedContinuousFunction.evalCLM ℂ (fun i => evI F (z i)) ∘L
      SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ _), fun f => by simp [l, pureA, evI, mul_comm]⟩
  exact (hs.cont l hl' Φ h1).comp (continuous_subtype_val.prodMk continuous_const)

end PositivityTheory.ThKCT

end
