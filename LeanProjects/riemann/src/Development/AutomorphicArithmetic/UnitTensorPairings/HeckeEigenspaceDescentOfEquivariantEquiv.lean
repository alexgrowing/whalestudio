import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTwistSideFormsLeSpanGoodLiftForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearDescentToBaseChangeOfFormStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

private theorem joint_zero {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : ι → V →ₗ[K] V) (p : ι → Prop) (ev : ι → K) (M : Finset (ι → K)) :
    ∀ y : V, (∀ μ ∈ M, ∃ t, p t ∧ μ t ≠ ev t) → (∀ t, p t → T t y = ev t • y) →
      y ∈ Submodule.span K {z | ∃ μ ∈ M, ∀ t, p t → T t z = μ t • z} → y = 0 := by
  classical
  induction M using Finset.induction_on with
  | empty =>
    intro y _ _ hs
    have : {z : V | ∃ μ ∈ (∅ : Finset (ι → K)), ∀ t, p t → T t z = μ t • z} = ∅ := by
      ext z; simp
    rw [this, Submodule.span_empty, Submodule.mem_bot] at hs
    exact hs
  | insert μ0 M _ ih =>
    intro y hne hy hs
    obtain ⟨t0, hp0, hμ0⟩ := hne μ0 (Finset.mem_insert_self _ _)
    let L : V →ₗ[K] V := T t0 - μ0 t0 • LinearMap.id
    have hL : Submodule.span K {z | ∃ μ ∈ insert μ0 M, ∀ t, p t → T t z = μ t • z} ≤
        (Submodule.span K {z | ∃ μ ∈ M, ∀ t, p t → T t z = μ t • z}).comap L := by
      rw [Submodule.span_le]
      rintro z ⟨μ, hμ, hz⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      rcases Finset.mem_insert.1 hμ with rfl | hμ
      · have : L z = 0 := by
          simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hz t0 hp0, sub_self]
        rw [this]; exact Submodule.zero_mem _
      · have : L z = (μ t0 - μ0 t0) • z := by
          simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hz t0 hp0, sub_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, hμ, hz⟩)
    have hLy : L y = (ev t0 - μ0 t0) • y := by
      simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hy t0 hp0, sub_smul]
    have h0 := ih ((ev t0 - μ0 t0) • y) (fun μ hμ => hne μ (Finset.mem_insert_of_mem hμ))
      (fun t ht => by rw [map_smul, hy t ht, smul_comm]) (hLy ▸ hL hs)
    rcases smul_eq_zero.1 h0 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hμ0
    · exact h

open scoped TensorProduct in
private theorem desc_exists (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (i : D.ntw.Tw) (j : ℕ) (b : Bool)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    ∃ (rd : ↥D.LL0 →+* FractionRing (D.ntw.O i)) (Φ : S.WL j →+ Fm S i j b), (∀ c, rd c = readLL0 S i b c) ∧
      (∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = rd c • Φ x) ∧
      (∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actG S i j b (In.rho j h1 h2) (In.chi j h1 h2) g (Φ x)) ∧
      (∀ k P x, Φ (In.hL j k P x) = hkF D S i j b (In.hL j) (In.hs j h1 h2) k P (Φ x)) ∧
      Submodule.span (FractionRing (D.ntw.O i)) (Set.range Φ) = ⊤ := by
  obtain ⟨n, bs, hb, -, hKs, hLi, hLs⟩ := In.ks j h1 h2
  obtain ⟨Φ, hc, hf, hw⟩ := GlobalTheory.T.exists_semilinear_descent_to_baseChange_of_form D.LL0 S.kKs S.kKs_spec (S.A j).WK bs hb hKs hLi hLs
    (KT := KB S i b) (readLL0 S i b) (fun s => rfl)
  refine ⟨readLL0 S i b, Φ, fun _ => rfl, hc, fun g x => ?_, fun k P x => ?_, ?_⟩
  · have e1 : actL D S j g x = (((chiL S j (In.chi j h1 h2) (S.eG.symm g))⁻¹ : ↥D.LL0) : D.what₂.LL) •
        (S.A j).ρ (S.eG.symm g) x := by
      simp only [actL, chiL, IntermediateField.coe_inv, LinearMap.smul_apply]
    have e2 := hc ((chiL S j (In.chi j h1 h2) (S.eG.symm g))⁻¹) ((S.A j).ρ (S.eG.symm g) x)
    rw [← e1, hf ((S.A j).ρ (S.eG.symm g)) (rhoKG S j (In.rho j h1 h2) (S.eG.symm g)) (fun w => rfl), map_inv₀] at e2
    exact e2
  · exact hf (In.hL j k P) _ (fun w => rfl) x
  · refine top_le_iff.1 ?_
    have h := GlobalTheory.HeightCounting.FormsSpan.span_one_tmul (R := S.Ks) (A := KB S i b) (M := ↥(S.A j).WK)
    refine (le_of_eq h.symm).trans (Submodule.span_mono ?_)
    rintro _ ⟨w, rfl⟩
    exact ⟨(w : S.WL j), hw w⟩

open GlobalTheory.HeightCounting.FormsSpan Formalism.MainNotions.IntegralHeckeForms in
private theorem hermFramePairNormalForm_frameSpan_le_of_generators (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (hU : D.nexp.U = Formalism.IndefR.NX.U D.nd)
    (hψ : PsiLaw D S In.θ) (i : D.ntw.Tw) (j : ℕ) (b : Bool)
    (rd : ↥D.LL0 →+* FractionRing (D.ntw.O i)) (Ψ : S.WL j →+ D.nexp.Fm i j b) (hrd : ∀ c, rd c = readLL0 S i b c)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Ψ ((c : D.what₂.LL) • x) = rd c • Ψ x)
    (ha : ∀ (g : G0g D.nd) (x : S.WL j), Ψ (actL D S j g x) = D.nexp.actG i j b g (Ψ x))
    (hs : Submodule.span (FractionRing (D.ntw.O i)) (Set.range Ψ) = ⊤) :
    V0 D.nexp i j b ≤ Submodule.span (FractionRing (D.ntw.O i)) (Ψ '' (goodL D S In.θ j : Set (S.WL j))) := by
  classical
  letI : Fintype (G0g D.nd) := finiteLevelGroupFintype D
  letI : Fintype ↥(Formalism.IndefR.NX.U D.nd) := fintypeU
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
  let pr : Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
    ∑ u : ↥(Formalism.IndefR.NX.U D.nd), rd (cU D In.θ u) • (D.nexp.actG i j b u).toLinearMap
  have hpr : ∀ w, pr (Ψ w) = Ψ (projL (S := S) In.θ j w) := fun w => by
    simp only [pr, projL, LinearMap.sum_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, map_sum, hc, ha]
  have hE : ∀ x, eG D.nexp i j b (Ψ x) = Ψ (opL D S j (GlobalTheory.HeightCounting.FormsStep.eL D) x) := fun x => by
    rw [opL_eL, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum, eG, MonoidAlgebra.lift_apply,
      Finsupp.sum_fintype _ _ (by intros; simp), LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hc, ha, D.nexp.eAlg_def, hrd]
    rfl
  have hfix : pr z = z := by
    have hu : ∀ u : ↥(Formalism.IndefR.NX.U D.nd), D.nexp.actG i j b u z =
        rd ((psiUOf D.nd (NX.xiRed D) In.θ u : (↥D.LL0)ˣ) : ↥D.LL0) • z := by
      intro u
      have hu' : (u : G0g D.nd) ∈ D.nexp.U := by rw [hU]; exact u.2
      have h := (Submodule.mem_iInf _).mp hz ⟨u, hu'⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, hψ i b u hu' u.2, ← hrd] at h
      exact h
    simp only [pr, LinearMap.sum_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, hu, smul_smul, ← map_mul]
    have hcu : ∀ u : ↥(Formalism.IndefR.NX.U D.nd), cU D In.θ u * ((psiUOf D.nd (NX.xiRed D) In.θ u : (↥D.LL0)ˣ) : ↥D.LL0) =
        (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ := by
      intro u
      unfold cU
      rw [map_inv, Units.val_inv_eq_inv_val]
      have h0 : ((psiUOf D.nd (NX.xiRed D) In.θ u : (↥D.LL0)ˣ) : ↥D.LL0) ≠ 0 := Units.ne_zero _
      field_simp
    simp only [hcu, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul (FractionRing (D.ntw.O i)), smul_smul]
    have hne : rd (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0) ≠ 0 := by
      refine (map_ne_zero rd).mpr fun h => ?_
      have h' := congrArg (fun x : ↥D.LL0 => (x : D.what₂.LL)) h
      exact Fintype.card_ne_zero (by exact_mod_cast h')
    have h1 : ((Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ℕ) : FractionRing (D.ntw.O i)) *
        rd (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ = 1 := by
      rw [map_inv₀, ← map_natCast rd]
      exact mul_inv_cancel₀ hne
    rw [h1, one_smul]
  rw [← hfix]
  have key : Submodule.span (FractionRing (D.ntw.O i)) (Set.range Ψ) ≤
      (Submodule.span (FractionRing (D.ntw.O i)) (Ψ '' (goodL D S In.θ j : Set (S.WL j)))).comap
        (eG D.nexp i j b ∘ₗ pr) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨w, rfl⟩
    change eG D.nexp i j b (pr (Ψ w)) ∈
      Submodule.span (FractionRing (D.ntw.O i)) (Ψ '' (goodL D S In.θ j : Set (S.WL j)))
    rw [hpr, hE]
    exact Submodule.subset_span ⟨_, goodL_of (GlobalTheory.HeightCounting.FormsStep.eIdem_all D) In.θ j w, rfl⟩
  exact key (Submodule.eq_top_iff'.mp hs z)

theorem UpperTheory.heckeEigenspace_descent_of_equivariant_equiv :
    ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S), D.nexp.U = Formalism.IndefR.NX.U D.nd → PsiLaw D S In.θ → (∀ i, In.Sb ⊆ D.ntw.S0 i) → ∀ (c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) (eF : ∀ i j b, 1 ≤ j → j ≤ D.R.m → D.nexp.Fm i j b ≃ₗ[FractionRing (D.ntw.O i)] Fm S i j b), (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (g : G0g D.nd) (y : D.nexp.Fm i j b), eF i j b h1 h2 (D.nexp.actG i j b g y) = actG S i j b (In.rho j h1 h2) (In.chi j h1 h2) g (eF i j b h1 h2 y)) → (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host) (y : D.nexp.Fm i j b), P ∉ D.ntw.S0 i → IsSplitPl D.host P → k ≤ D.R.r → eF i j b h1 h2 (D.nexp.hkF i j b k P y) = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (c i b P) ^ k • hkF D S i j b (In.hL j) (In.hs j h1 h2) k P (eF i j b h1 h2 y)) → ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), 1 ≤ j → j ≤ D.R.m → ∀ ev : ℕ → PlE D.host → FractionRing (D.ntw.O i), GlobalTheory.EigTie.IsEigSys D.nexp i j b ev → ∃ σ : D.what₂.FT, D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ ∧ ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i → ev k P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (c i b P) ^ k * (show FractionRing (D.ntw.O i) from readLL0 S i b (In.eig j σ k P)) := by
  intro D S In hU hψ hSb c eF hact hhk i j b h1 h2 ev hev
  classical
  obtain ⟨y, hyV, hy0, hyE⟩ := hev
  obtain ⟨rd, Φ, hrd, hc, ha, hh, hs⟩ := desc_exists D S In i j b h1 h2
  set e := eF i j b h1 h2 with he
  let Ψ : S.WL j →+ D.nexp.Fm i j b := e.symm.toLinearMap.toAddMonoidHom.comp Φ
  have hΨ : ∀ x, e (Ψ x) = Φ x := fun x => e.apply_symm_apply _
  have hc' : ∀ (c : ↥D.LL0) (x : S.WL j), Ψ ((c : D.what₂.LL) • x) = rd c • Ψ x := fun c x => by
    apply e.injective
    rw [hΨ, hc, map_smul, hΨ]
  have ha' : ∀ (g : G0g D.nd) (x : S.WL j), Ψ (actL D S j g x) = D.nexp.actG i j b g (Ψ x) := fun g x => by
    apply e.injective
    rw [hact i j b h1 h2, hΨ, hΨ, ha]
  have hs' : Submodule.span (FractionRing (D.ntw.O i)) (Set.range Ψ) = ⊤ := by
    have : Set.range Ψ = e.symm.toLinearMap '' Set.range Φ := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, hs, Submodule.map_top, LinearEquiv.range]
  have hle := hermFramePairNormalForm_frameSpan_le_of_generators D S In hU hψ i j b rd Ψ hrd hc' ha' hs' hyV
  by_contra hno
  apply hy0
  let sys : D.what₂.FT → ℕ × PlE D.host → FractionRing (D.ntw.O i) := fun σ t =>
    algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (c i b t.2) ^ t.1 * rd (In.eig j σ t.1 t.2)
  have hfin : {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}.Finite := Set.toFinite _
  refine joint_zero (fun t : ℕ × PlE D.host => D.nexp.hkF i j b t.1 t.2) (fun t => Formalism.MainNotions.IntegralHeckeForms.HkIdx i t.1 t.2)
    (fun t => ev t.1 t.2) (hfin.toFinset.image sys) y ?_ (fun t ht => hyE t.1 t.2 ht) (Submodule.span_le.mpr ?_ hle)
  · intro μ hμ
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hμ
    rw [Set.Finite.mem_toFinset] at hσ
    by_contra hne
    push_neg at hne
    refine hno ⟨σ, hσ.1, hσ.2, fun k P a1 a2 a3 a4 => ?_⟩
    have := hne (k, P) ⟨a1, a2, a3, a4⟩
    simp only [sys, hrd] at this
    exact this.symm
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe]
    refine Submodule.iSup_induction (motive := fun y => Ψ y ∈ _) _ (In.span j h1 h2 hx) ?_ ?_ ?_
    · intro σ w hw
      refine Submodule.iSup_induction (motive := fun y => Ψ y ∈ _) _ hw ?_ ?_ ?_
      · intro hσ z hz
        refine Submodule.subset_span ⟨sys σ, Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hσ), ?_⟩
        rintro ⟨k, P⟩ ⟨a1, a2, a3, a4⟩
        have hz2 := (Submodule.mem_inf.1 hz).2
        simp only [Submodule.mem_iInf] at hz2
        have h3 := Module.End.mem_eigenspace_iff.1 (hz2 k P ⟨a1, a2, a3, fun h => a4 (hSb i h)⟩)
        apply e.injective
        simp only [sys]
        rw [hhk i j b h1 h2 k P _ a4 a3 a2, map_smul, hΨ, ← hh, h3, hc, mul_smul]
      · rw [map_zero]; exact zero_mem _
      · intro y z hy hz; rw [map_add]; exact add_mem hy hz
    · rw [map_zero]; exact zero_mem _
    · intro y z hy hz; rw [map_add]; exact add_mem hy hz
