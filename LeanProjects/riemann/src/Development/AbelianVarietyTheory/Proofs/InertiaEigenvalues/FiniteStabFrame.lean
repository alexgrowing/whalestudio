import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStabMono
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetMassEqRelIndexMulMass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDoubleCosetsConjMaxCompact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantHermitianWeightForm
import Development.AbelianVarietyTheory.Definitions.Divisors.MemStdLatticeIffIntegralCoords
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.AddCharThetaLawRearrangementIdentity
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.CoefDuty GlobalTheory.TwoLattices GlobalTheory.ClassRefine GlobalTheory.ClassPet
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FormInner

theorem wsum_transport {A G Γ W I : Type} [Group A] [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Fintype I]
    (ι : Γ →* G) (hι : Function.Injective ι) (φ : A ≃* G) (J : Subgroup G) (y : I → G) (hy : Formalism.IndefR.Bridge.IsReps ι J y) :
    ∃ T, Reps (ι.range.comap φ.toMonoidHom) (J.comap φ.toMonoidHom) T ∧ ∀ F F' : G → W,
      wsum (ι.range.comap φ.toMonoidHom) (J.comap φ.toMonoidHom) T (fun g => inner ℂ (F (φ g)) (F' (φ g))) =
        Formalism.IndefR.Bridge.adInner ι J y F F' := by
  classical
  have hinj : Function.Injective fun i => φ.symm (y i) := fun i j e => by
    have e' : y i = y j := φ.symm.injective e
    exact (hy (y i)).unique ⟨1, 1, by simp⟩ ⟨1, 1, by simp [e']⟩
  have key : ∀ g i, (∃ (γ : ι.range.comap φ.toMonoidHom) (κ : A), κ ∈ J.comap φ.toMonoidHom ∧ g = (γ : A) * φ.symm (y i) * κ) ↔
      ∃ (γ : Γ) (k : J), φ g = ι γ * y i * k := fun g i => by
    constructor
    · rintro ⟨γ, κ, hκ, rfl⟩
      obtain ⟨δ, hδ⟩ := γ.2
      exact ⟨δ, ⟨φ κ, hκ⟩, by simp [hδ]⟩
    · rintro ⟨γ, k, e⟩
      refine ⟨⟨φ.symm (ι γ), ⟨γ, by simp⟩⟩, φ.symm k, by simp, φ.injective (by simp [e])⟩
  refine ⟨Finset.univ.image fun i => φ.symm (y i), fun g => ?_, fun F F' => ?_⟩
  · obtain ⟨i, hi, hu⟩ := hy (φ g)
    refine ⟨φ.symm (y i), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key g i).2 hi⟩, ?_⟩
    rintro t ⟨ht, h⟩
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ht
    rw [hu j ((key g j).1 h)]
  · rw [wsum, Finset.sum_image fun i _ j _ e => hinj e, Formalism.IndefR.Bridge.adInner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MulEquiv.apply_symm_apply]
    congr 3
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun δ : Formalism.IndefR.Bridge.stab ι J (y i) =>
      (⟨⟨φ.symm (ι δ), ⟨δ, by simp⟩⟩, mem_stabQ.2 (by simpa using (Formalism.IndefR.Bridge.mem_stab ι).1 δ.2)⟩ :
        stabQ (ι.range.comap φ.toMonoidHom) (J.comap φ.toMonoidHom) (φ.symm (y i)))) ⟨fun δ δ' e => ?_, fun γ => ?_⟩)
    · exact Subtype.ext (hι (φ.symm.injective (congrArg (fun z => (z.1 : A)) e)))
    · obtain ⟨δ, hδ⟩ := γ.1.2
      refine ⟨⟨δ, (Formalism.IndefR.Bridge.mem_stab ι).2 ?_⟩, Subtype.ext (Subtype.ext (by simp [hδ]))⟩
      simpa [hδ] using mem_stabQ.1 γ.2

section Std

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem relIndex_ne_zero_of_cover' {G : Type} [Group G] {H K : Subgroup G} (F : Finset G) (hF : ∀ κ ∈ K, ∃ f ∈ F, f⁻¹ * κ ∈ H) :
    H.relIndex K ≠ 0 := by
  classical
  have : ∀ f₀ ∈ F, ∃ u, (∃ κ ∈ K, f₀⁻¹ * κ ∈ H) → u ∈ K ∧ f₀⁻¹ * u ∈ H := fun f₀ _ => by
    by_cases h : ∃ κ ∈ K, f₀⁻¹ * κ ∈ H
    · obtain ⟨u, hu⟩ := h
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose! u hu using this
  rw [← Subgroup.inf_relIndex_right]
  refine relIndex_ne_zero_of_cover (F.image u) (fun κ hκ => ?_) inf_le_right
  obtain ⟨f₀, h₀, h₁⟩ := hF κ hκ
  obtain ⟨h2, h3⟩ := hu f₀ h₀ ⟨κ, hκ, h₁⟩
  refine ⟨u f₀, Finset.mem_image_of_mem _ h₀, ?_, K.mul_mem (K.inv_mem h2) hκ⟩
  have := H.mul_mem (H.inv_mem h3) h₁
  simpa [mul_assoc] using this

theorem bounded_of_le {J : Subgroup (GAf L n)} (h : J ≤ ReciprocityTheory.Aut.Umax L n) : IsBounded J :=
  ⟨{1}, fun κ hκ => ⟨1, by simp, by simpa using h hκ⟩⟩

theorem congSub_relIndex {J : Subgroup (GAf L n)} (hJ : IsBounded J) {N : ℕ} (hN : 0 < N) : (congSub L n N).relIndex J ≠ 0 := by
  obtain ⟨F, hF⟩ := (GlobalTheory.CongIndex.finite_index_conj L n J hJ 1 N hN).2.1
  exact relIndex_ne_zero_of_cover' F hF

theorem relIndex_of_le {G : Type} [Group G] {H H' K : Subgroup G} (h : H ≤ H') (hne : H.relIndex K ≠ 0) : H'.relIndex K ≠ 0 :=
  fun h0 => hne (Subgroup.relIndex_eq_zero_of_le_left h h0)

theorem relIndex_of_le' {G : Type} [Group G] {H K K' : Subgroup G} (h : K' ≤ K) (hne : H.relIndex K ≠ 0) : H.relIndex K' ≠ 0 :=
  fun h0 => hne (Subgroup.relIndex_eq_zero_of_le_right h h0)

theorem cj_relIndex {K : Subgroup (GAf L n)} (hle : K ≤ ReciprocityTheory.Aut.Umax L n) (hne : K.relIndex (ReciprocityTheory.Aut.Umax L n) ≠ 0) (x) :
    (TwoLattices.cj K x).relIndex K ≠ 0 := by
  obtain ⟨N, hN, h⟩ := (GlobalTheory.CongIndex.finite_index_conj L n _ (bounded_of_le le_rfl) x 1 one_pos).1
  have h1 : (TwoLattices.cj (ReciprocityTheory.Aut.Umax L n) x).relIndex (ReciprocityTheory.Aut.Umax L n) ≠ 0 :=
    relIndex_of_le (fun κ hκ => mem_cj.2 (h κ hκ).1) (congSub_relIndex (bounded_of_le le_rfl) hN)
  have h2 : (TwoLattices.cj K x).relIndex (TwoLattices.cj (ReciprocityTheory.Aut.Umax L n) x) ≠ 0 := by
    rw [TwoLattices.cj, TwoLattices.cj, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective (MulAut.conj x⁻¹).surjective]
    exact hne
  exact relIndex_of_le' hle (Subgroup.relIndex_ne_zero_trans h2 h1)

theorem cover_umax : Cover (ReciprocityTheory.Aut.GQ L n) (ReciprocityTheory.Aut.Umax L n) := by
  obtain ⟨T, hT⟩ := GlobalTheory.ClassFinConj.exists_finset_double_cosets_conj L n 1
  exact ⟨T, fun g => by obtain ⟨γ, hγ, t, ht, κ, hκ, e⟩ := hT g; exact ⟨t, ht, ⟨γ, hγ⟩, κ, hκ.1, e⟩⟩

theorem finite_stabQ {J : Subgroup (GAf L n)} (hJ : IsBounded J) (t) : Finite (stabQ (ReciprocityTheory.Aut.GQ L n) J t) :=
  (Equiv.subtypeEquivRight fun _ => mem_stabQ).finite_iff.2 (GlobalTheory.StabFin.finite_conj_mem L n J hJ t)

theorem relIndex_of_cover {G : Type} [Group G] {Γ K U : Subgroup G} (hle : K ≤ U) (hc : Cover Γ K)
    (hf : ∀ t, Finite (stabQ Γ U t)) : K.relIndex U ≠ 0 := by
  obtain ⟨S, hS⟩ := hc
  refine (GlobalTheory.UnimodMass.mass_eq_relIndex_mul Γ K U hle (GlobalTheory.UnimodMass.finite_dc_of_cover ⟨S, fun g => ?_⟩)
    fun t => (Equiv.subtypeEquivRight fun _ => mem_stabQ).finite_iff.1 (hf t)).1
  obtain ⟨s, hs, γ, κ, hκ, e⟩ := hS g
  exact ⟨γ, γ.2, s, hs, κ, hκ, e⟩

theorem classSum_eq_wsum (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) (J : Subgroup (GAf L n)) (T : Finset (GAf L n))
    (f f' : GAf L n → a.W) : classSum a β J T f f' = wsum (ReciprocityTheory.Aut.GQ L n) J T fun g => β (f g) (f' g) := by
  simp only [classSum, wsum, card_stabQ_eq]

theorem span_values (a : NG.AlgWt L n) {f : GAf L n → a.W} (hf : f ∈ NG.AFall L n a.ρ) (h₀ : f ≠ 0) :
    Submodule.span ℂ (Set.range f) = ⊤ := by
  let U : Subrepresentation a.ρ := ⟨Submodule.span ℂ (Set.range f), fun g w hw => by
    refine Submodule.span_induction (p := fun w _ => a.ρ g w ∈ Submodule.span ℂ (Set.range f)) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, hf.1 g h⟩
    · simp
    · intro a b _ _ ha hb
      rw [map_add]; exact add_mem ha hb
    · intro c a _ ha
      rw [map_smul]; exact Submodule.smul_mem _ c ha⟩
  have hU : U = ⊤ := by
    haveI := a.irr
    refine (eq_bot_or_eq_top U).resolve_left fun hb => h₀ ?_
    funext g
    have : f g ∈ U.toSubmodule := Submodule.subset_span ⟨g, rfl⟩
    rw [hb] at this
    exact this
  exact congrArg Subrepresentation.toSubmodule hU

theorem span_finite_values (a : NG.AlgWt L n) {f : GAf L n → a.W} (hf : f ∈ NG.AFall L n a.ρ) (h₀ : f ≠ 0) :
    ∃ (m : ℕ) (g : Fin m → GAf L n), Submodule.span ℂ (Set.range fun i => f (g i)) = ⊤ := by
  obtain ⟨_, ι, _, _, b, -⟩ := a.alg
  haveI : Module.Finite ℂ a.W := Module.Finite.of_basis b
  have h := span_values a hf h₀
  obtain ⟨s, hs, hsp, hli⟩ := exists_linearIndependent ℂ (Set.range f)
  haveI : Finite s := hli.finite
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin s
  choose g hg using fun v : s => hs v.2
  refine ⟨m, fun i => g (e.symm i), ?_⟩
  rw [← h, ← hsp]
  congr 1
  ext v
  exact ⟨by rintro ⟨i, rfl⟩; simp only [hg]; exact (e.symm i).2, fun hv => ⟨e ⟨v, hv⟩, by simp [hg]⟩⟩

end Std

variable {D : D7} {μ : D.what₂.Tup} {j : ℕ} (X : MtReal D μ j) {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] (ι : Γ →* G) (φ : GAf D.host.E D.R.nV ≃* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ)
  (e : X.wt.W ≃ₗ[ℂ] W) (Fm : D.what₂.Mt μ j → G → W)

theorem classSum_of_frame {I : Type} [Fintype I] (y : I → G) (hy : Bridge.IsReps ι J y) (hι : Function.Injective ι)
    (hfin : ∀ t, Finite (stabQ (ι.range.comap φ.toMonoidHom) (ReciprocityTheory.Aut.Umax D.host.E D.R.nV) t))
    (hρ : ∀ δ (a b : W), inner ℂ (ρ δ a) (ρ δ b) = inner ℂ a b)
    (hJ : J.comap φ.toMonoidHom ≤ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) (hX : IsBounded X.J)
    (hFm : ∀ x, Fm x ∈ Bridge.AdForms ι ρ J χ) (hread : ∀ x g, e (X.real x g) = Fm x (φ g))
    (c : ℝ) (hc : 0 < c) (hip : ∀ x x' : D.what₂.Mt μ j, inner ℂ x x' = (c : ℂ) * Bridge.adInner ι J y (Fm x) (Fm x')) :
    ClassSum X := by
  have hA : ∀ x, X.real x ∈ NG.TypeSp X.wt.ρ X.J X.χ := fun x => X.real_range ▸ LinearMap.mem_range_self _ x
  obtain ⟨N, hN, hNJ⟩ := X.J_open
  obtain ⟨T', hT', htr⟩ := wsum_transport (W := W) ι hι φ J y hy
  set Γ₂ := ι.range.comap φ.toMonoidHom with hΓ₂
  set J₂ := J.comap φ.toMonoidHom with hJ₂
  have hNU := congSub_relIndex (bounded_of_le (le_refl (ReciprocityTheory.Aut.Umax D.host.E D.R.nV))) hN
  have hJU : J₂.relIndex (ReciprocityTheory.Aut.Umax D.host.E D.R.nV) ≠ 0 := relIndex_of_cover hJ hT'.cover hfin
  set K := congSub D.host.E D.R.nV N ⊓ J₂ with hK
  have hKU : K.relIndex (ReciprocityTheory.Aut.Umax D.host.E D.R.nV) ≠ 0 := Subgroup.relIndex_inf_ne_zero hNU hJU
  have hKle : K ≤ ReciprocityTheory.Aut.Umax D.host.E D.R.nV := inf_le_right.trans hJ
  have hKJ : K ≤ X.J := fun κ hκ => (hNJ κ hκ.1).1
  have hc₁ : Cover (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) K := cover_umax.of_relIndex hKU
  have hK₁ : K.relIndex X.J ≠ 0 := relIndex_of_cover hKJ hc₁ (finite_stabQ hX)
  have hK₂ : K.relIndex J₂ ≠ 0 := relIndex_of_le' hJ hKU
  have hc₂ : Cover Γ₂ K := hT'.cover.of_relIndex hK₂
  obtain ⟨T, hT⟩ := (hc₁.mono hKJ).reps
  refine ⟨hX, ?_⟩
  by_cases hz : ∀ x : D.what₂.Mt μ j, x = 0
  · obtain ⟨β, hβ⟩ := GlobalTheory.InvFormBdd.exists_isInvForm _ _ X.wt
    refine ⟨β, T, 1, hβ, hT, one_pos, fun x x' => ?_⟩
    rw [hz x]
    simp [classSum]
  obtain ⟨x₀, h₀⟩ := not_forall.1 hz
  obtain ⟨m, g, hg⟩ := span_finite_values X.wt (hA x₀).1 fun h => h₀ (X.real_inj (by rw [h, map_zero]))
  have hl₂ : ∀ δ γ, ι δ = φ γ → ∀ x g, e (X.real x (γ * g)) = ρ δ (e (X.real x g)) := fun δ γ h x g => by
    have := hFm x δ (φ g) 1
    rw [hread, hread, map_mul, ← h]
    simpa using this
  have hinv : ∀ γ ∈ Γ₂, ∀ x x' g g', pullForm X e (X.real x (γ * g)) (X.real x' (γ * g')) =
      pullForm X e (X.real x g) (X.real x' g') := by
    rintro γ ⟨δ, hδ⟩ x x' g g'
    rw [pullForm_apply, pullForm_apply, hl₂ δ γ hδ, hl₂ δ γ hδ, hρ]
  obtain ⟨β, c', hβ, hc', hβ₁, hsum⟩ := exists_form (f := fun x => X.real x) (p := fun i => (x₀, g i)) hg
    (cj_relIndex hKle hKU) (fun κ hκ x g => by
      obtain ⟨h1, h2⟩ := hNJ κ hκ.1
      have := congrFun ((hA x).2 ⟨κ, h1⟩) g
      rw [h2, Units.val_one, one_smul] at this
      exact this)
    (le_acts fun γ hγ => ⟨X.wt.ρ ⟨γ, hγ⟩, fun x g => (hA x).1.1 ⟨γ, hγ⟩ g⟩)
    (le_acts (Γ := Γ₂) fun γ ⟨δ, hδ⟩ => ⟨e.symm.toLinearMap ∘ₗ ρ δ ∘ₗ e.toLinearMap, fun x g => e.injective (by
      rw [hl₂ δ γ hδ]; simp)⟩)
    hc₁ hc₂ (finite_stabQ (bounded_of_le hKle)) (fun t => finite_stab_mono le_rfl hKle t (hfin t)) (b := pullForm X e)
    ⟨fun a b => by rw [pullForm_apply, pullForm_apply, inner_conj_symm], fun a ha => by
      rw [pullForm_apply]
      exact (re_inner_self_pos (𝕜 := ℂ) (x := e a)).2 (fun h => ha (e.map_eq_zero_iff.1 h))⟩ hinv
  have hβ' : IsInvForm X.wt β := by
    refine ⟨hβ.1, hβ.2, fun γ a b => ?_⟩
    have : (β.comp (X.wt.ρ γ)).compl₂ (X.wt.ρ γ) = β := LinearMap.ext_on_range hg fun i => LinearMap.ext_on_range hg fun k => by
      show β (X.wt.ρ γ _) (X.wt.ρ γ _) = _
      rw [← (hA x₀).1.1, ← (hA x₀).1.1]
      exact hβ₁ γ γ.2 x₀ x₀ _ _
    exact LinearMap.congr_fun₂ this a b
  have hB : ∀ x, X.real x ∈ NG.TypeSp X.wt.ρ J₂ (χ.comp (φ.toMonoidHom.subgroupComap J)) := fun x =>
    ⟨(hA x).1, fun κ => funext fun g => e.injective (by
      have := hFm x 1 (φ g) ⟨φ κ, κ.2⟩
      show e (X.real x (g * κ)) = e (((χ ⟨φ κ, κ.2⟩ : ℂˣ) : ℂ) • X.real x g)
      rw [map_smul, hread, hread, map_mul]
      simpa using this)⟩
  have p₁ : (0 : ℝ) < K.relIndex X.J := Nat.cast_pos.2 (Nat.pos_of_ne_zero hK₁)
  have p₂ : (0 : ℝ) < K.relIndex J₂ := Nat.cast_pos.2 (Nat.pos_of_ne_zero hK₂)
  refine ⟨β, T, c * (c' * K.relIndex X.J / K.relIndex J₂), hβ', hT, by positivity, fun x x' => ?_⟩
  have r₁ := form_inv β hX (hA x) (hA x')
  have r₂ := form_inv (pullForm X e) (bounded_of_le hJ) (hB x) (hB x')
  have l₁ : ∀ (γ : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) g, β (X.real x (γ * g)) (X.real x' (γ * g)) = β (X.real x g) (X.real x' g) :=
    fun γ g => hβ₁ γ γ.2 x x' g g
  have l₂ : ∀ (γ : Γ₂) g, pullForm X e (X.real x (γ * g)) (X.real x' (γ * g)) = pullForm X e (X.real x g) (X.real x' g) :=
    fun γ g => hinv γ γ.2 x x' g g
  have e₀ := hsum x x'
  rw [dsum_index inf_le_right hK₂ hc₂ l₂ r₂, dsum_index hKJ hK₁ hc₁ l₁ r₁, dsum_eq hT' l₂ r₂, dsum_eq hT l₁ r₁] at e₀
  simp only [pullForm_apply, hread] at e₀
  have n₂ : ((K.relIndex J₂ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hK₂
  rw [hip, ← htr, classSum_eq_wsum, eq_div_of_mul_eq n₂ ((mul_comm _ _).trans e₀)]
  push_cast
  ring

theorem finite_stab_frame {V : HSp D} {n : ℕ} (hV : GlobalTheory.StdFrame.OrthFrame V) {hF : D.host.F = maximalRealSubfield D.host.E}
    {P : principalLevelFrame.RowPsi V n} (hP : GlobalTheory.Mem.R3.StdFrame hF P) (t) :
    Finite (stabQ ((Bridge.ratF V).range.comap (frameEquiv P).toMonoidHom) (ReciprocityTheory.Aut.Umax D.host.E n) t) := by
  let P₀ := GlobalTheory.StdFrameModel.unitPsi hV.gram_eq
  have h₀ := (GlobalTheory.StdFrameModel.stdPsi_unitPsi hV).2
  have hrat : RatFrame P₀ := fun g => by simpa using GlobalTheory.NJoin.Inh.rat_unit hV.gram_eq g
  let θ := (frameEquiv P).trans (frameEquiv P₀).symm
  have hθ : ∀ κ, frameEquiv P₀ (θ κ) = frameEquiv P κ := fun κ => (frameEquiv P₀).apply_symm_apply _
  have hU : ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, θ κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank := fun κ hκ => by
    rw [h₀, TopMult.lift_unique (P₀.into (θ κ)) (P.into κ) (hθ κ)]
    exact (hP.2 κ).1 hκ
  haveI := finite_stabQ (bounded_of_le (le_refl (ReciprocityTheory.Aut.Umax D.host.E V.rank))) (θ t)
  refine Finite.of_injective (β := stabQ (ReciprocityTheory.Aut.GQ D.host.E V.rank) (ReciprocityTheory.Aut.Umax D.host.E V.rank) (θ t))
    (fun γ => ⟨⟨θ γ.1, (hrat.iff _).2 (by rw [hθ]; exact γ.1.2)⟩, mem_stabQ.2 (by simpa using hU _ (mem_stabQ.1 γ.2))⟩)
    fun a b h => Subtype.ext (Subtype.ext (θ.injective (congrArg (fun z => (z.1 : GAf D.host.E V.rank)) h)))

end GlobalTheory.FormInner

end
