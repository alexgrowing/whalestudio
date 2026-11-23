import Formalism.LocalToGlobal.GlobalTheory.GL4.LowerSlopeInequalityFamily
import Formalism.LocalToGlobal.Columns.BrzoPairAtZeroRight
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps

theorem hTV0 (D : D7) (u : D.what₂.Word) : TSpan D.what₂.LL ((D.fm u).lam 0) = VV D.what₂.LL ((D.fm u).lam 0) :=
  translate_span_eq D.what₂.LL D.what₂.Tau (D.R.N 0) ((D.fm u).lam 0)

section Orth

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

open Classical in

def prjC (c : (D.mem u).C.cls 0) : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] ((D.fm u).lat 0).V :=
  ((coE CV (hTV0 D u)).symm : ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)) →ₗ[D.what₂.LL] ((D.fm u).lat 0).V) ∘ₗ
    (LinearMap.single D.what₂.LL (fun _ : (D.mem u).C.cls 0 => VV D.what₂.LL ((D.fm u).lam 0)) c ∘ₗ
      (LinearMap.proj c ∘ₗ (coE CV (hTV0 D u) : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)))))

open Classical in
theorem co_prjC (c c' : (D.mem u).C.cls 0) (x : ((D.fm u).lat 0).V) :
    CV.co (prjC CV c x) c' = if c' = c then CV.co x c else 0 := by
  have hE : ∀ (y : ((D.fm u).lat 0).V) (c'' : (D.mem u).C.cls 0),
      CV.co y c'' = ((coE CV (hTV0 D u) y c'' : VV D.what₂.LL ((D.fm u).lam 0)) : _) := fun _ _ => rfl
  have hP : coE CV (hTV0 D u) (prjC CV c x) = Pi.single c (coE CV (hTV0 D u) x c) := by
    simp [prjC]
  rw [hE, hP, hE x c]
  by_cases h : c' = c
  · subst h
    simp
  · simp [h]

private theorem coE_prjC_self (c : (D.mem u).C.cls 0) (x : ((D.fm u).lat 0).V) :
    coE CV (hTV0 D u) (prjC CV c x) c = coE CV (hTV0 D u) x c := by
  classical
  simp [prjC]

private theorem coE_prjC_of_ne_eq_zero (c c' : (D.mem u).C.cls 0) (x : ((D.fm u).lat 0).V) (h : c' ≠ c) :
    coE CV (hTV0 D u) (prjC CV c x) c' = 0 := by
  classical
  simp [prjC, h]

theorem prjC_sum (x : ((D.fm u).lat 0).V) : ∑ c, prjC CV c x = x := by
  apply (coE CV (hTV0 D u)).injective
  funext c'
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single c']
  · exact coE_prjC_self CV c' x
  · intro b _ hb
    exact coE_prjC_of_ne_eq_zero CV b c' x (Ne.symm hb)
  · intro h
    exact absurd (Finset.mem_univ _) h

def NC (c : (D.mem u).C.cls 0) : Submodule (𝓞 D.what₂.LL) ((D.fm u).lat 0).V :=
  ((D.fm u).lat 0).L.map ((prjC CV c).restrictScalars (𝓞 D.what₂.LL))

theorem prjC_mem (c : (D.mem u).C.cls 0) {x : ((D.fm u).lat 0).V} (hx : x ∈ ((D.fm u).lat 0).L) :
    prjC CV c x ∈ ((D.fm u).lat 0).L := by
  refine Formalism.L2.Ker.mem_of_forall_locP _ fun Q => ?_
  obtain ⟨w, rfl⟩ : ∃ w, D.plEq w = Q := ⟨D.plEq.symm Q, D.plEq.apply_symm_apply Q⟩
  rw [mem_localization_iff_localizationAtPlace]
  have hγ : ∀ c τ, ∃ γ, LocBasis D w (CV.Q c τ) (CV.eQ c τ) γ := fun c τ =>
    exists_locBasis w (CV.Q c τ) (CV.Q_good c τ) (CV.eQ c τ)
  choose γ hγ using hγ
  have hxw : x ∈ locW D.what₂.places w ((D.fm u).lat 0).L := Submodule.subset_span hx
  rw [CV.fin w γ hγ] at hxw
  rw [CV.fin w γ hγ]
  intro c'
  rw [co_prjC]
  split_ifs with h
  · subst h
    exact hxw c'
  · have e : actAll ((D.fm u).lam 0) (fun τ => (γ c' τ)⁻¹) (0 : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL) = 0 := by
      simp [actAll]
    rw [e]
    exact zero_mem _

theorem iSup_NC : (⨆ c, NC CV c) = ((D.fm u).lat 0).L := by
  apply le_antisymm
  · refine iSup_le fun c => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact prjC_mem CV c hx
  · intro x hx
    rw [← prjC_sum CV x]
    exact Submodule.sum_mem _ fun c _ => Submodule.mem_iSup_of_mem c ⟨x, hx, rfl⟩

theorem tcAt_eq_zero {v : InfinitePlace D.what₂.LL} {c : (D.mem u).C.cls 0} {x : ((D.fm u).lat 0).V} (h : CV.co x c = 0) :
    tcAt CV v c x = 0 := by
  simp [tcAt, h]

theorem NC_orth (c c' : (D.mem u).C.cls 0) (hcc : c ≠ c') :
    ∀ x ∈ NC CV c, ∀ y ∈ NC CV c', ∀ v, majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y = 0 := by
  rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ v
  simp only [LinearMap.restrictScalars_apply]
  rw [majorant_lattice_eq_sum CV]
  refine Finset.sum_eq_zero fun c'' _ => ?_
  by_cases h : c'' = c
  · subst h
    have : tcAt CV v c'' (prjC CV c' y) = 0 := tcAt_eq_zero CV (by rw [co_prjC, if_neg hcc])
    rw [this, nfAll_zero_left]
  · have : tcAt CV v c'' (prjC CV c x) = 0 := tcAt_eq_zero CV (by rw [co_prjC, if_neg h])
    rw [this, nfAll_zero_right]

theorem injOn_NC (c : (D.mem u).C.cls 0) {W : Type} [AddCommGroup W] [Module D.what₂.LL W]
    (ψ : VV D.what₂.LL ((D.fm u).lam 0) →ₗ[D.what₂.LL] W) (hψ : Function.Injective ψ) :
    Set.InjOn (ψ ∘ₗ (LinearMap.proj c ∘ₗ (coE CV (hTV0 D u) : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0))))) (NC CV c) := by
  rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ hxy
  have h := hψ hxy
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
    LinearMap.coe_proj, Function.eval] at h ⊢
  apply (coE CV (hTV0 D u)).injective
  funext c'
  by_cases hc : c' = c
  · subst hc
    exact h
  · rw [coE_prjC_of_ne_eq_zero CV c c' x hc, coE_prjC_of_ne_eq_zero CV c c' y hc]

end Orth

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps

section Rank

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem vv_finite_pos (D : D7) (u : D.what₂.Word) :
    Module.Finite D.what₂.LL (VV D.what₂.LL ((D.fm u).lam 0)) ∧ 0 < finrank D.what₂.LL (VV D.what₂.LL ((D.fm u).lam 0)) := by
  obtain ⟨Z, -, hne, -, -⟩ := standard_basis_z D.what₂.Tau (D.R.N 0) ((D.fm u).lam 0)
  have := Z.fin
  exact ⟨Module.Finite.of_basis (Z.basis D.what₂.LL), by rw [Module.finrank_eq_card_basis (Z.basis D.what₂.LL)]; exact Fintype.card_pos⟩

theorem range_prjC (c : (D.mem u).C.cls 0) :
    finrank D.what₂.LL (LinearMap.range (prjC CV c)) = finrank D.what₂.LL (VV D.what₂.LL ((D.fm u).lam 0)) := by
  classical
  have hsurj : LinearMap.range (LinearMap.proj c ∘ₗ (coE CV (hTV0 D u) : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)))) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro z
    refine ⟨(coE CV (hTV0 D u)).symm (Pi.single c z), ?_⟩
    simp
  unfold prjC
  rw [← LinearMap.comp_assoc, LinearMap.range_comp_of_range_eq_top _ hsurj]
  apply LinearMap.finrank_range_of_inj
  rw [LinearMap.coe_comp]
  exact (coE CV (hTV0 D u)).symm.injective.comp (by simpa using Pi.single_injective c)

theorem rk_NC (c : (D.mem u).C.cls 0) : rkK (NC CV c) = finrank D.what₂.LL (VV D.what₂.LL ((D.fm u).lam 0)) := by
  unfold Formalism.HN.rkK NC
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, ((D.fm u).lat_good 0).2.2, Submodule.map_top]
  exact range_prjC CV c

theorem rank_lattice_level_zero (CV : ColVal D u) : rkK ((D.fm u).lat 0).L =
    Fintype.card ((D.mem u).C.cls 0) * finrank D.what₂.LL (VV D.what₂.LL ((D.fm u).lam 0)) := by
  obtain ⟨hfin, -⟩ := vv_finite_pos D u
  unfold Formalism.HN.rkK
  rw [((D.fm u).lat_good 0).2.2, finrank_top, LinearEquiv.finrank_eq (coE CV (hTV0 D u)), Module.finrank_pi_fintype,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem NC_ne_bot (c : (D.mem u).C.cls 0) : NC CV c ≠ ⊥ := by
  intro h0
  have h1 := rk_NC CV c
  rw [h0] at h1
  have h2 : Formalism.HN.rkK (⊥ : Submodule (𝓞 D.what₂.LL) ((D.fm u).lat 0).V) = 0 := by
    unfold Formalism.HN.rkK
    rw [Submodule.bot_coe, Submodule.span_zero_singleton, finrank_bot]
  have := (vv_finite_pos D u).2
  omega

theorem muMax_le_class : ∃ c, ((D.fm u).lat 0).muMax ≤ (withL ((D.fm u).lat 0) (NC CV c)).muMax := by
  classical
  have : Nonempty ((D.mem u).C.cls 0) := CV.ne
  have key := Formalism.L2.Col.hlat_orth_sum (A := (D.fm u).lat 0) (NC CV) ((D.fm u).lat_good 0).1
    (fun c => ((D.fm u).lat_good 0).2.1.map _) (NC_ne_bot CV) (NC_orth CV)
    (finrank D.what₂.LL (VV D.what₂.LL ((D.fm u).lam 0))) (vv_finite_pos D u).2 (rk_NC CV)
    (by rw [iSup_NC CV]; exact rank_lattice_level_zero CV)
  obtain ⟨c, hc⟩ := key.2
  rw [iSup_NC CV] at hc
  exact ⟨c, hc⟩

end Rank

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SlopeMaxClass (D : D7) : Prop :=
  ∀ u (CV : ColVal D u) (c : (D.mem u).C.cls 0), (∃ y : Fin (D.R.N 0) → (D.sp.X 0).V, Formalism.MainNotions.flipTwoThree.ShortAt D u c y) →
    (withL ((D.fm u).lat 0) (NC CV c)).muMax ≤
      ∑ τ, (colAbsP D u τ * Real.log (4 * (D.R.k : ℝ) ^ 4 * D.host.v ^ 2) +
        Real.log (cNu ((D.fm u).lam 0 τ).natW) - (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u))

theorem slopeMaxGiven_of_class (D : D7) (h : SlopeMaxClass D) : SlopeMaxGiven D := by
  intro u CV hs
  obtain ⟨c, hc⟩ := muMax_le_class CV
  exact hc.trans (h u CV c (hs c))

theorem third_proposition_of_class (h : ∀ D, SlopeMaxClass D) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : ConclusionF6 Fm :=
  family_third_bound_of_max_slope Fm ⟨0, fun x _ _ i => slopeMaxGiven_of_class _ (h _)⟩

theorem Link6F_of_class (h : ∀ D, SlopeMaxClass D) : Link6F :=
  fun _ Fm _ _ _ => third_proposition_of_class h Fm

theorem packet_of_slope_max_class (h : ∀ D, SlopeMaxClass D) : KudlaFamilyOfMinkowskiTransference :=
  packet_of_third_proposition (Link6F_of_class h)

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
