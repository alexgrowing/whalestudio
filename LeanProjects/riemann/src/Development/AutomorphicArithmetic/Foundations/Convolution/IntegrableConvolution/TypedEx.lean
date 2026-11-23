import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.FixedOpen

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory

namespace UpperTheory.ConvolutionTheory.L1

section Abs

variable {G L H : Type} [Group G] [TopologicalSpace G] [Group L] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private lemma comm_apply {A B : H →L[ℂ] H} (h : Commute A B) (v : H) : A (B v) = B (A v) :=
  congrArg (fun T : H →L[ℂ] H => T v) h.eq

private lemma comm_eig_abs {R T : H →L[ℂ] H} {c : ℂ} {u : H} (h : R (T u) = T (R u)) (h3 : R u = c • u) :
    R (T u) = c • T u := by
  rw [h, h3, map_smul]

private lemma comm_rep (π : UnitaryRep G H) {a b : G} (h : a * b = b * a) : Commute (π a) (π b) :=
  ContinuousLinearMap.ext fun v => by
    show π a (π b v) = π b (π a v)
    rw [← π.map_mul_apply, h, π.map_mul_apply]

private lemma comm_prj (π : UnitaryRep G H) {V : Submodule ℂ H} (hcl : IsClosed (V : Set H))
    (hinv : π.IsInvariant V) (g : G) : Commute (prj V) (π g) := by
  have h : π.IsInvariant V.topologicalClosure := by
    rw [hcl.submodule_topologicalClosure_eq]
    exact hinv
  exact ((UnitaryRep.isInvariant_iff_commute_starProjection (π := π) V.topologicalClosure).1 h g).symm

private lemma mem_of_comm {V : Submodule ℂ H} (hcl : IsClosed (V : Set H)) {e : H →L[ℂ] H}
    (h : Commute (prj V) e) {v : H} (hv : v ∈ V) : e v ∈ V := by
  have hfix : prj V v = v := Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure _ hv)
  have e1 : prj V (e v) = e v := by
    have := comm_apply h v
    rwa [hfix] at this
  have h2 := Submodule.starProjection_eq_self_iff.1 e1
  rwa [hcl.submodule_topologicalClosure_eq] at h2

private lemma prj_self {W : Submodule ℂ H} {v : H} (hv : v ∈ W) : prj W v = v :=
  Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure _ hv)

private lemma prj_mem' {W : Submodule ℂ H} (hW : IsClosed (W : Set H)) (v : H) : prj W v ∈ W := by
  have : prj W v ∈ W.topologicalClosure := Submodule.starProjection_apply_mem _ v
  rwa [hW.submodule_topologicalClosure_eq] at this

private theorem key_abs (π : UnitaryRep G H) {V : Submodule ℂ H} (hcl : IsClosed (V : Set H)) (hinv : π.IsInvariant V)
    (hirr : ∀ V' ≤ V, IsClosed (V' : Set H) → π.IsInvariant V' → V' = ⊥ ∨ V' = V)
    (φ : L →* G) (e : H →L[ℂ] H)
    (hc : ∀ y : G, (∀ g, φ g * y = y * φ g) → ∀ v, π y (e v) = e (π y v))
    (hdec : ∀ x : G, ∃ (a b : G) (g : L), (∀ g', φ g' * a = a * φ g') ∧ (∀ g', φ g' * b = b * φ g') ∧ x = a * φ g * b)
    {z : H} (hz : z ∈ V) (hz0 : z ≠ 0) (hez : e z = z)
    (N : Submodule ℂ H) (hNV : N ≤ V) (hN : N ≠ ⊥) (hst : ∀ g, ∀ u ∈ N, π (φ g) u ∈ N) :
    ∃ u ∈ N, e u ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  let M : Submodule ℂ H :=
    { carrier := {u | u ∈ V ∧ ∀ g, e (π (φ g) u) = 0}
      add_mem' := fun {a b} ha hb => ⟨V.add_mem ha.1 hb.1, fun g => by
        rw [map_add, map_add, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨V.zero_mem, fun g => by simp⟩
      smul_mem' := fun c a ha => ⟨V.smul_mem c ha.1, fun g => by
        rw [map_smul, map_smul, ha.2, smul_zero]⟩ }
  have hMmem : ∀ u, u ∈ M ↔ u ∈ V ∧ ∀ g, e (π (φ g) u) = 0 := fun u => Iff.rfl
  have hMcl : IsClosed (M : Set H) := by
    have : (M : Set H) = (V : Set H) ∩ ⋂ g, {u | e (π (φ g) u) = 0} := by
      ext u
      simp [hMmem]
    rw [this]
    exact hcl.inter (isClosed_iInter fun g =>
      isClosed_eq (e.continuous.comp (π (φ g)).continuous) continuous_const)
  have hMy : ∀ y : G, (∀ g, φ g * y = y * φ g) → ∀ u ∈ M, π y u ∈ M := by
    intro y hy u hu
    refine (hMmem _).2 ⟨hinv _ _ hu.1, fun g => ?_⟩
    rw [← π.map_mul_apply, hy, π.map_mul_apply, ← hc y hy, hu.2, map_zero]
  have hMl : ∀ g', ∀ u ∈ M, π (φ g') u ∈ M := by
    intro g' u hu
    refine (hMmem _).2 ⟨hinv _ _ hu.1, fun g => ?_⟩
    rw [← π.map_mul_apply, ← map_mul]
    exact hu.2 _
  have hMinv : π.IsInvariant M := by
    intro x u hu
    obtain ⟨a, b, g, ha, hb, rfl⟩ := hdec x
    rw [π.map_mul_apply, π.map_mul_apply]
    exact hMy a ha _ (hMl g _ (hMy b hb _ hu))
  have hNM : N ≤ M := fun u hu => ⟨hNV hu, fun g => hcon _ (hst g u hu)⟩
  rcases hirr M (fun u hu => hu.1) hMcl hMinv with hb | ht
  · exact hN (eq_bot_iff.2 (hb ▸ hNM))
  · have hzM : z ∈ M := ht ▸ hz
    have h1 := hzM.2 1
    rw [map_one, π.map_one_apply, hez] at h1
    exact hz0 h1

private theorem exists_fixed_abs {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [TotallyDisconnectedSpace Γ] [T2Space Γ] (σ : UnitaryRep Γ H) {V : Submodule ℂ H} (hcl : IsClosed (V : Set H))
    (hinv : σ.IsInvariant V) (hne : V ≠ ⊥) :
    ∃ U : Subgroup Γ, IsOpen (U : Set Γ) ∧ ∃ e ∈ V, e ≠ 0 ∧ ∀ u ∈ U, σ u e = e := by
  classical
  let _ : MeasurableSpace Γ := borel Γ
  have _ : BorelSpace Γ := ⟨rfl⟩
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hpos : 0 < ‖v‖ / 2 := half_pos (norm_pos_iff.2 hv0)
  have hN : IsOpen {g : Γ | ‖σ g v - v‖ < ‖v‖ / 2} :=
    isOpen_lt ((σ.continuous_orbit v).sub continuous_const).norm continuous_const
  have h1N : (1 : Γ) ∈ {g : Γ | ‖σ g v - v‖ < ‖v‖ / 2} := by
    simp only [Set.mem_setOf_eq, σ.map_one_apply, sub_self, norm_zero]
    exact hpos
  obtain ⟨Hh, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hN h1N
  set U : Subgroup Γ := Hh.toOpenSubgroup.toSubgroup with hUdef
  have hU : IsOpen (U : Set Γ) := Hh.toOpenSubgroup.isOpen
  have hUN : ∀ u ∈ U, ‖σ u v - v‖ < ‖v‖ / 2 := fun u hu => hH hu
  have _ : CompactSpace U := isCompact_iff_compactSpace.1 (U.isClosed_of_isOpen hU).isCompact
  set ρ : Measure U := CuspidalSpectrum.haarProb U with hρ
  have hcont : Continuous fun u : U => σ (u : Γ) v := (σ.continuous_orbit v).comp continuous_subtype_val
  have hint : Integrable (fun u : U => σ (u : Γ) v) ρ :=
    integrableOn_univ.1 (hcont.continuousOn.integrableOn_compact isCompact_univ)
  set e : H := ∫ u : U, σ (u : Γ) v ∂ρ with hedef
  have heV : e ∈ V :=
    Convex.integral_mem (V.restrictScalars ℝ).convex hcl (ae_of_all _ fun u => hinv _ _ hv) hint
  have hefix : ∀ u ∈ U, σ u e = e := by
    intro u hu
    rw [hedef, ← (σ u).integral_comp_comm hint]
    have := integral_mul_left_eq_self (μ := ρ) (fun x : U => σ (x : Γ) v) ⟨u, hu⟩
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [Subgroup.coe_mul]
    rw [σ.map_mul_apply]
  have hdiff : e - v = ∫ u : U, (σ (u : Γ) v - v) ∂ρ := by
    rw [integral_sub hint (integrable_const v), integral_const, probReal_univ, one_smul]
  have hle : ‖e - v‖ ≤ ‖v‖ / 2 := by
    rw [hdiff]
    calc ‖∫ u : U, (σ (u : Γ) v - v) ∂ρ‖ ≤ ‖v‖ / 2 * ρ.real Set.univ :=
          norm_integral_le_of_norm_le_const (ae_of_all _ fun u => (hUN u u.2).le)
      _ = ‖v‖ / 2 := by rw [probReal_univ, mul_one]
  refine ⟨U, hU, e, heV, fun h0 => ?_, hefix⟩
  rw [h0, zero_sub, norm_neg] at hle
  linarith

end Abs

section Conc

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem exists_off_open (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))) :
    ∃ I : Finset (Pl K), ∀ w ∉ I, ∀ x ∈ GLnLocal.integralGL (w.adicCompletion K) n,
      ∃ u ∈ U, (u : AdelicGLn.FiniteAdelicGL K n) = AdelicGLn.localEmbedding w x := by
  classical
  set Φ := AdelicGLn.finiteRestrictedEquiv K n with hΦ
  have hopen : ∀ v : Pl K,
      IsOpen (GLnLocal.integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K))) :=
    fun v => GLnLocal.isOpen_integralGL (v.adicCompletion K) n
  set U' : Set (AdelicGLn.FiniteAdelicGL K n) := Subtype.val '' (U : Set (AdelicGLn.integralFiniteGL K n)) with hU'
  have hU'o : IsOpen U' := (AdelicGLn.isOpen_integralFiniteGL K n).isOpenMap_subtype_val _ hU
  have h1U : U' ∈ 𝓝 (1 : AdelicGLn.FiniteAdelicGL K n) := hU'o.mem_nhds ⟨1, U.one_mem, rfl⟩
  have : Fact (∀ v : Pl K,
      IsOpen (GLnLocal.integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))) :=
    ⟨hopen⟩
  have hV : Φ.symm ⁻¹' U' ∈ 𝓝 (1 : AdelicGLn.FiniteRestrictedGL K n) :=
    Φ.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using h1U)
  have h1 : (1 : AdelicGLn.FiniteRestrictedGL K n) =
      RestrictedProduct.structureMap _ (fun v : Pl K => (GLnLocal.integralGL (v.adicCompletion K) n :
        Set (GL (Fin n) (v.adicCompletion K)))) cofinite 1 := rfl
  rw [h1, RestrictedProduct.nhds_eq_map_structureMap hopen, Filter.mem_map, nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, hI, t, ht, hsub⟩ := hV
  refine ⟨hI.toFinset, fun w hw x hx => ?_⟩
  obtain ⟨-, l1, l2, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K n w
  have e : ∀ (v : Pl K) (y : AdelicGLn.FiniteAdelicGL K n), finAt v (finEmb K n y) = Φ y v := fun _ _ => rfl
  have hmem : ∀ v, Φ (AdelicGLn.localEmbedding w x) v ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
    intro v
    rw [← e]
    by_cases hv : v = w
    · subst hv
      rw [l1]
      exact hx
    · rw [l2 v hv]
      exact one_mem _
  let y : Π v : Pl K, (GLnLocal.integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K))) :=
    fun v => ⟨Φ (AdelicGLn.localEmbedding w x) v, hmem v⟩
  have hy : RestrictedProduct.structureMap _ _ cofinite y = Φ (AdelicGLn.localEmbedding w x) :=
    RestrictedProduct.ext _ _ fun v => rfl
  have hyI : y ∈ (I : Set (Pl K)).pi t := by
    intro v hv
    have hvw : v ≠ w := fun h => hw (by rw [← h]; exact hI.mem_toFinset.2 hv)
    have : y v = 1 := Subtype.ext (by
      show Φ (AdelicGLn.localEmbedding w x) v = 1
      rw [← e, l2 v hvw])
    rw [this]
    exact mem_of_mem_nhds (ht v)
  have h2 := hsub hyI
  simp only [Set.mem_preimage, hy] at h2
  rw [ContinuousMulEquiv.symm_apply_apply] at h2
  obtain ⟨u, huU, hu⟩ := h2
  exact ⟨u, huU, hu⟩

private abbrev phi (w : Pl K) : Gw n w →* normOneGL K n :=
  (MultiplicityOne.finProj K n).comp (AdelicGLn.localEmbedding w)

private theorem dec_phi (b : Pl K) (x : normOneGL K n) :
    ∃ (a c : normOneGL K n) (g : Gw n b), (∀ g', phi b g' * a = a * phi b g') ∧
      (∀ g', phi b g' * c = c * phi b g') ∧ x = a * phi b g * c := by
  obtain ⟨A', h, rfl⟩ := MultiplicityOne.exists_archProj_mul_finProj x
  obtain ⟨-, h1, -, -, h5⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K n b
  obtain ⟨h₀, hh₀⟩ : ∃ h₀, h₀ = finAt b (finEmb K n h) := ⟨_, rfl⟩
  obtain ⟨h', hh'⟩ : ∃ h', h' = (AdelicGLn.localEmbedding b h₀)⁻¹ * h := ⟨_, rfl⟩
  have hd : h = AdelicGLn.localEmbedding b h₀ * h' := by rw [hh', mul_inv_cancel_left]
  have hf : finAt b (finEmb K n h') = 1 := by
    rw [hh', map_mul, map_inv, finAt_mul, finAt_inv, h1, ← hh₀, inv_mul_cancel]
  refine ⟨archProj K n A', MultiplicityOne.finProj K n h', h₀, fun g => ?_, fun g => ?_, ?_⟩
  · rw [MonoidHom.comp_apply]
    exact MultiplicityOne.finProj_mul_archProj_comm (AdelicGLn.localEmbedding b g) A'
  · simp only [phi, MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, h5 h' hf g]
  · simp only [phi, MonoidHom.comp_apply]
    rw [mul_assoc, ← map_mul, ← hd]

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

private theorem mem_eigL' {w : Pl K} {J : Subgroup (Gw n w)} {χ : Gw n w → ℂ} {x : LL μ} :
    x ∈ eigL μ w J χ ↔ ∀ g ∈ J, rhoL μ w g x = χ g • x := by
  simp [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus]

private lemma rhoL_eq (w : Pl K) (g : Gw n w) : rhoL μ w g = rightRegularRep (rationalGLOne K n) μ (phi w g) := rfl

private theorem exists_off {V : Submodule ℂ (LL μ)} (hV : IsSummand μ V) :
    ∃ (I : Finset (Pl K)) (e : LL μ), e ∈ V ∧ e ≠ 0 ∧
      ∀ w ∉ I, ∀ x ∈ GLnLocal.integralGL (w.adicCompletion K) n, rhoL μ w x e = e := by
  obtain ⟨U, hU, e, heV, he0, hfix⟩ := exists_fixed_abs
    ((rightRegularRep (rationalGLOne K n) μ).comapHom (finOne K n) continuous_finOne) hV.closed
    (fun g v hv => hV.inv _ v hv) hV.ne_bot
  obtain ⟨I, hI⟩ := exists_off_open U hU
  refine ⟨I, e, heV, he0, fun w hw x hx => ?_⟩
  obtain ⟨u, huU, hu⟩ := hI w hw x hx
  have h1 : rightRegularRep (rationalGLOne K n) μ (finOne K n u) e = e := hfix u huU
  have h2 : phi w x = finOne K n u := by
    rw [← MultiplicityOne.finProj_eq_finOne, hu]
    rfl
  rw [rhoL_eq, h2, h1]

private theorem step {V : Submodule ℂ (LL μ)} (hV : IsSummand μ V) (J : ∀ w : Pl K, Subgroup (Gw n w))
    (χ : ∀ w : Pl K, Gw n w → ℂ) (hJχ : ∀ w, CO (J w) ∧ IsChr (J w) (χ w))
    (hne : ∀ w, V ⊓ eigL μ w (J w) (χ w) ≠ ⊥) (A : Set (Pl K)) (b : Pl K) (hb : b ∉ A)
    (h : ∃ u : LL μ, u ≠ 0 ∧ u ∈ V ∧ ∀ w ∈ A, u ∈ eigL μ w (J w) (χ w)) :
    ∃ u : LL μ, u ≠ 0 ∧ u ∈ V ∧ ∀ w ∈ insert b A, u ∈ eigL μ w (J w) (χ w) := by
  obtain ⟨u₀, hu₀, hu₀V, hu₀A⟩ := h
  set N : Submodule ℂ (LL μ) := V ⊓ ⨅ w ∈ A, eigL μ w (J w) (χ w) with hNdef
  have hmemN : ∀ u, u ∈ N ↔ u ∈ V ∧ ∀ w ∈ A, u ∈ eigL μ w (J w) (χ w) := fun u => by
    simp [hNdef, Submodule.mem_inf, Submodule.mem_iInf]
  have hcb := (eigBasic K n μ b (J b) (χ b) (hJχ b).1 (hJχ b).2).2.2.2
  have hc : ∀ y : normOneGL K n, (∀ g, phi b g * y = y * phi b g) → ∀ v,
      rightRegularRep (rationalGLOne K n) μ y (prj (eigL μ b (J b) (χ b)) v) =
        prj (eigL μ b (J b) (χ b)) (rightRegularRep (rationalGLOne K n) μ y v) := fun y hy v =>
    comm_apply (hcb _ fun x _ => comm_rep _ (hy x).symm) v
  have hphi : ∀ w, w ≠ b → ∀ (g : Gw n w) (g' : Gw n b), phi b g' * phi w g = phi w g * phi b g' := by
    intro w hw g g'
    have := (UpperTheory.ConvolutionTheory.Tf.locEmb K n b).2.2.2.1 w hw g' g
    simp only [phi, MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, this]
  have hdec := dec_phi (K := K) (n := n) b
  obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).1 (hne b)
  have hst : ∀ g, ∀ u ∈ N, rightRegularRep (rationalGLOne K n) μ (phi b g) u ∈ N := by
    intro g u hu
    obtain ⟨h1, h2⟩ := (hmemN u).1 hu
    refine (hmemN _).2 ⟨hV.inv _ _ h1, fun w hw => (mem_eigL' μ).2 fun x hx => ?_⟩
    have hwb : w ≠ b := fun e => hb (e ▸ hw)
    have h3 : rhoL μ w x u = χ w x • u := (mem_eigL' μ).1 (h2 w hw) x hx
    have h4 : rhoL μ w x (rightRegularRep (rationalGLOne K n) μ (phi b g) u) =
        rightRegularRep (rationalGLOne K n) μ (phi b g) (rhoL μ w x u) := by
      rw [rhoL_eq μ w x]
      exact comm_apply (comm_rep _ (hphi w hwb x g).symm) u
    exact comm_eig_abs h4 h3
  obtain ⟨u, hu, hu0⟩ := key_abs (rightRegularRep (rationalGLOne K n) μ) hV.closed hV.inv hV.irred (phi b)
    (prj (eigL μ b (J b) (χ b))) hc hdec hz.1 hz0 (prj_self hz.2) N inf_le_left
    ((Submodule.ne_bot_iff _).2 ⟨u₀, (hmemN _).2 ⟨hu₀V, hu₀A⟩, hu₀⟩) hst
  obtain ⟨h1, h2⟩ := (hmemN u).1 hu
  refine ⟨_, hu0, mem_of_comm hV.closed (hcb _ fun x _ => comm_prj _ hV.closed hV.inv (phi b x)) h1, fun w hw => ?_⟩
  rcases hw with rfl | hw
  · exact prj_mem' (eigBasic K n μ w (J w) (χ w) (hJχ w).1 (hJχ w).2).1 u
  · have hwb : w ≠ b := fun e => hb (e ▸ hw)
    refine (mem_eigL' μ).2 fun x hx => ?_
    have h3 : rhoL μ w x u = χ w x • u := (mem_eigL' μ).1 (h2 w hw) x hx
    have h4 : rhoL μ w x (prj (eigL μ b (J b) (χ b)) u) = prj (eigL μ b (J b) (χ b)) (rhoL μ w x u) := by
      rw [rhoL_eq μ w x]
      exact hc _ (fun g => hphi w hwb x g) u
    exact comm_eig_abs h4 h3

end Conc

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.typedEx :
    UpperTheory.ConvolutionTheory.L1.TypedEx := by
  intro K _ _ n μ _ V hV J χ hJχ hcof hne
  classical
  obtain ⟨I, e, heV, he0, hfix⟩ := UpperTheory.ConvolutionTheory.L1.exists_off μ hV
  have hb := Filter.eventually_cofinite.1 hcof
  set S : Finset (Pl K) := I ∪ hb.toFinset with hS
  have hbase : ∃ u : LL μ, u ≠ 0 ∧ u ∈ V ∧ ∀ w ∈ ((S : Set (Pl K))ᶜ), u ∈ eigL μ w (J w) (χ w) := by
    refine ⟨e, he0, heV, fun w hw => (UpperTheory.ConvolutionTheory.L1.mem_eigL' μ).2 fun g hg => ?_⟩
    have hw1 : w ∉ I := fun h => hw (Finset.mem_coe.2 (Finset.mem_union_left _ h))
    have hw2 : w ∉ hb.toFinset := fun h => hw (Finset.mem_coe.2 (Finset.mem_union_right _ h))
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw2
    rw [hw2.1] at hg
    rw [hfix w hw1 g hg, hw2.2]
    simp
  have hall : ∀ F : Finset (Pl K), ∃ u : LL μ, u ≠ 0 ∧ u ∈ V ∧
      ∀ w ∈ ((S : Set (Pl K))ᶜ ∪ (F : Set (Pl K))), u ∈ eigL μ w (J w) (χ w) := by
    intro F
    induction F using Finset.induction_on with
    | empty => simpa using hbase
    | insert b F hbF ih =>
      by_cases hbA : b ∈ ((S : Set (Pl K))ᶜ ∪ (F : Set (Pl K)))
      · obtain ⟨u, h1, h2, h3⟩ := ih
        refine ⟨u, h1, h2, fun w hw => h3 w ?_⟩
        rcases hw with hw | hw
        · exact Or.inl hw
        · rcases Finset.mem_insert.1 (Finset.mem_coe.1 hw) with rfl | hw
          · exact hbA
          · exact Or.inr hw
      · obtain ⟨u, h1, h2, h3⟩ := UpperTheory.ConvolutionTheory.L1.step μ hV J χ hJχ hne _ b hbA ih
        refine ⟨u, h1, h2, fun w hw => h3 w ?_⟩
        rcases hw with hw | hw
        · exact Or.inr (Or.inl hw)
        · rcases Finset.mem_insert.1 (Finset.mem_coe.1 hw) with rfl | hw
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hw)
  obtain ⟨u, h1, h2, h3⟩ := hall S
  refine (Submodule.ne_bot_iff _).2 ⟨u, Submodule.mem_inf.2 ⟨h2, ?_⟩, h1⟩
  simp only [Submodule.mem_iInf]
  intro w
  refine h3 w ?_
  by_cases hw : w ∈ (S : Set (Pl K))
  · exact Or.inr hw
  · exact Or.inl hw
