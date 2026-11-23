import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.ArchimedeanDenseStabilizers.DenseRangeOfNotIsReal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHeightBasePairEqModuleProduct
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.LocalToGlobal.IndefiniteReal.CoreTExist
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open scoped TensorProduct Matrix Pointwise

noncomputable section

namespace CompanionTheory.Rg.FlSep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem conj_emb (v : HeightOneSpectrum (𝓞 F)) (g : GAd σ J) (x : GLoc σ J v) :
    g * emb σ J v x * g⁻¹ = emb σ J v (proj σ J v g * x * (proj σ J v g)⁻¹) :=
  GAd_ext σ J (fun w => by simp) fun u => by
    by_cases h : u = v
    · subst h; simp
    · simp [proj_emb_ne σ J h]

theorem normal_emb (v : HeightOneSpectrum (𝓞 F)) : (emb σ J v).range.Normal :=
  ⟨fun _ hx g => by
    obtain ⟨x, rfl⟩ := hx
    exact ⟨_, (conj_emb σ J v g x).symm⟩⟩

theorem ratLoc_injective (u : HeightOneSpectrum (𝓞 F)) : Function.Injective (ratLoc σ J u) := fun a b h =>
  Subtype.ext (Units.ext (Matrix.ext fun r s => (inclR (F := F) (E := E) (Fv F u)).injective
    (congrArg (fun x => (HA.mat _ _ _ x).1 r s) h)))

def ratGroup (v : HeightOneSpectrum (𝓞 F)) (W : Subgroup (GAd σ J)) : Subgroup (GLoc σ J v) :=
  (((emb σ J v).range ⊔ W).comap (ratEmb σ J)).map (ratLoc σ J v)

variable {σ J}

theorem exists_of_mem_sup {v : HeightOneSpectrum (𝓞 F)} {W : Subgroup (GAd σ J)} {x : GAd σ J}
    (h : x ∈ (emb σ J v).range ⊔ W) : ∃ y, ∃ w ∈ W, x = emb σ J v y * w := by
  haveI := normal_emb σ J v
  have h' : x ∈ ((((emb σ J v).range ⊔ W : Subgroup (GAd σ J))) : Set (GAd σ J)) := h
  rw [Subgroup.normal_mul] at h'
  obtain ⟨_, ⟨y, rfl⟩, w, hw, rfl⟩ := Set.mem_mul.1 h'
  exact ⟨y, w, hw, rfl⟩

theorem emb_mem_levelOpen {L : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)} {k : GLoc σ J v}
    (hk : k ∈ stabLoc σ J L v) : emb σ J v k ∈ levelOpen σ J L := by
  refine mem_levelOpen.2 fun u => ?_
  by_cases e : u = v
  · subst e; simpa using hk
  · rw [proj_emb_ne σ J e]; exact one_mem _

theorem finite_coset {A : Subgroup (GAd σ J)} (hA : {γ : GRat σ J | ratEmb σ J γ ∈ A}.Finite) (g : GAd σ J) :
    {γ : GRat σ J | g⁻¹ * ratEmb σ J γ ∈ A}.Finite := by
  by_cases h : ∃ γ₀ : GRat σ J, g⁻¹ * ratEmb σ J γ₀ ∈ A
  · obtain ⟨γ₀, h0⟩ := h
    refine (hA.image fun b => γ₀ * b).subset fun γ hγ => ⟨γ₀⁻¹ * γ, ?_, by simp⟩
    have h1 := A.mul_mem (A.inv_mem h0) hγ
    have e : (g⁻¹ * ratEmb σ J γ₀)⁻¹ * (g⁻¹ * ratEmb σ J γ) = ratEmb σ J (γ₀⁻¹ * γ) := by
      rw [map_mul, map_inv]; group
    rw [e] at h1
    exact h1
  · refine Set.Finite.subset Set.finite_empty fun γ hγ => (h ⟨γ, hγ⟩).elim

theorem finite_local {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsLattice E L]
    (hB : {γ : GRat σ J | ratEmb σ J γ ∈ levelOpen σ J L}.Finite)
    {v : HeightOneSpectrum (𝓞 F)} {K : Subgroup (GLoc σ J v)} (hK : IsCompact (K : Set (GLoc σ J v)))
    {C : Set (GLoc σ J v)} (hC : IsCompact C) :
    {δ : GRat σ J | ratEmb σ J δ ∈ (emb σ J v).range ⊔ (levelOpen σ J L ⊓ K.comap (proj σ J v)) ∧
      ratLoc σ J v δ ∈ C}.Finite := by
  have hCK : IsCompact (C * (K : Set (GLoc σ J v))) := hC.mul hK
  obtain ⟨t, -, ht⟩ := hCK.elim_nhds_subcover (fun c => (fun y => c⁻¹ * y) ⁻¹' (stabLoc σ J L v : Set (GLoc σ J v)))
    (fun c _ => by
      have hc : Continuous fun y : GLoc σ J v => c⁻¹ * y := continuous_const.mul continuous_id
      exact hc.continuousAt.preimage_mem_nhds ((isOpen_stabLoc σ J L v).mem_nhds (by simp [one_mem])))
  refine Set.Finite.subset (Set.Finite.biUnion t.finite_toSet fun c _ => finite_coset hB (emb σ J v c)) ?_
  rintro δ ⟨h1, h2⟩
  obtain ⟨y, w, hw, e⟩ := exists_of_mem_sup h1
  have e1 : ratLoc σ J v δ = y * proj σ J v w := by
    rw [← proj_ratEmb, e, map_mul, proj_emb_self]
  have hy : y ∈ C * (K : Set (GLoc σ J v)) :=
    Set.mem_mul.2 ⟨_, h2, (proj σ J v w)⁻¹, K.inv_mem hw.2, by rw [e1]; group⟩
  have := ht hy
  simp only [Set.mem_iUnion, Set.mem_preimage] at this ⊢
  obtain ⟨c, hc, hcy⟩ := this
  refine ⟨c, hc, ?_⟩
  have e2 : (emb σ J v c)⁻¹ * ratEmb σ J δ = emb σ J v (c⁻¹ * y) * w := by
    rw [e, map_mul, map_inv, mul_assoc]
  show (emb σ J v c)⁻¹ * ratEmb σ J δ ∈ levelOpen σ J L
  rw [e2]
  exact mul_mem (emb_mem_levelOpen hcy) hw.1

theorem mem_orbit_of_eq {v : HeightOneSpectrum (𝓞 F)} {K : Subgroup (GLoc σ J v)} {W : Subgroup (GAd σ J)}
    (hW : W ≤ K.comap (proj σ J v)) {g g' : GLoc σ J v} {γ γ' : GRat σ J} {a w w' : GAd σ J} (hw : w ∈ W)
    (hw' : w' ∈ W) (e : emb σ J v g = ratEmb σ J γ * a * w) (e' : emb σ J v g' = ratEmb σ J γ' * a * w') :
    ∃ x ∈ ratGroup σ J v W, ∃ k ∈ K, x * g = g' * k := by
  have e1 : ratEmb σ J (γ' * γ⁻¹) = emb σ J v g' * (w'⁻¹ * w) * (emb σ J v g)⁻¹ := by
    rw [e, e', map_mul, map_inv]; group
  have hm : ratEmb σ J (γ' * γ⁻¹) ∈ (emb σ J v).range ⊔ W := by
    rw [e1]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left ⟨g', rfl⟩)
      (Subgroup.mem_sup_right (mul_mem (inv_mem hw') hw))) (inv_mem (Subgroup.mem_sup_left ⟨g, rfl⟩))
  refine ⟨_, ⟨_, hm, rfl⟩, proj σ J v (w'⁻¹ * w), hW (mul_mem (inv_mem hw') hw), ?_⟩
  have e2 : ratLoc σ J v (γ' * γ⁻¹) = g' * proj σ J v (w'⁻¹ * w) * g⁻¹ := by
    rw [← proj_ratEmb, e1, map_mul, map_mul, map_inv, proj_emb_self, proj_emb_self]
  rw [e2]
  group

theorem sigma_invol (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem exists_sigma_ne (h : IsCMExt F E σ) : ∃ z, σ z ≠ z := by
  by_contra hc
  push_neg at hc
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hr : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := h.2.2.2 τ x
    rw [hc x] at this
    simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm
  have h1 := h.2.1
  have := (NumberField.IsTotallyComplex.isComplex (K := E) (InfinitePlace.mk τ))
  exact (InfinitePlace.not_isReal_iff_isComplex.2 this) ((InfinitePlace.isReal_mk_iff).2 hr)

theorem mem_range_of_sigma_eq (h : IsCMExt F E σ) {y : E} (hy : σ y = y) : y ∈ (algebraMap F E).range := by
  by_contra hc
  obtain ⟨z, hz⟩ := exists_sigma_ne h
  have hli : LinearIndependent F ![(1 : E), y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simpa using hst
    · exfalso
      apply hc
      refine ⟨-s / t, ?_⟩
      have : t • y = -(s • (1 : E)) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hst
      have e : y = algebraMap F E (-s / t) := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at this
        have ht' : algebraMap F E t ≠ 0 := by simpa using ht
        rw [map_div₀, map_neg]
        field_simp
        rw [mul_comm, this]
      exact e.symm
  have hb := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h.2.2.1])
  have hspan : Submodule.span F (Set.range ![(1 : E), y]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [h.2.2.1])
  have hz' : z ∈ Submodule.span F (Set.range ![(1 : E), y]) := hspan ▸ Submodule.mem_top
  have hfix : ∀ w ∈ Submodule.span F (Set.range ![(1 : E), y]), σ w = w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      fin_cases i
      · simp
      · simpa using hy
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | smul c a _ ha =>
      have e : σ (c • a) = c • σ a := σ.toLinearMap.map_smul c a
      rw [e, ha]
  exact hz (hfix z hz')

theorem isTotDef_of_posDef (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hp : CompanionTheory.Rg.Fl.IsPosDef σ J) :
    Formalism.UG.IsTotDef σ J := by
  refine ⟨h.1, fun ι => Or.inl fun x hx => ?_⟩
  letI : Algebra F ℂ := (Complex.ofRealHom.comp ι).toAlgebra
  haveI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  let τ : E →ₐ[F] ℂ := IsAlgClosed.lift
  have hτ : ∀ a, τ (algebraMap F E a) = (ι a : ℂ) := fun a => τ.commutes a
  set y := Formalism.UG.hform (σ : E →+* E) J x x with hy
  have ey : y = dotProduct (fun i => σ (x i)) (J.mulVec x) := by
    simp only [hy, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rfl
  have hfix : σ y = y := by
    rw [ey]
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, sigma_invol h]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hJ.1 i j]
    ring
  obtain ⟨a, ha⟩ := mem_range_of_sigma_eq h hfix
  refine ⟨a, ha, ?_⟩
  have := hp x hx (τ : E →+* ℂ)
  rw [← ey, ← ha] at this
  have e2 : (τ : E →+* ℂ) (algebraMap F E a) = (ι a : ℂ) := hτ a
  rw [e2] at this
  simpa using this

@[reducible] def cmStarRing (h : IsCMExt F E σ) : StarRing E where
  star := σ
  star_involutive := sigma_invol h
  star_mul := fun a b => by rw [map_mul, mul_comm]
  star_add := map_add σ

theorem mulVec_fv (h : IsCMExt F E σ) (γ : GRat σ J) (x : Fin n → E) :
    (Formalism.MainNotions.StandardLattice.finMat σ J (ratEmb σ J γ)).mulVec (fun i => (1 : Af F) ⊗ₜ[F] x i) =
      fun i => (1 : Af F) ⊗ₜ[F] ((γ.1 : Matrix (Fin n) (Fin n) E).mulVec x) i := by
  letI := cmStarRing h
  have e := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.StabFin.finMat_rat σ J γ.1 (ratEmb σ J γ) rfl
  rw [e]
  funext i
  exact (RingHom.map_mulVec (inclR (Af F)) _ x i).symm

theorem stab_of_mem_levelOpen (h : IsCMExt F E σ) {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsLattice E L]
    {γ : GRat σ J} (hg : ratEmb σ J γ ∈ levelOpen σ J L) (x : Fin n → E) :
    x ∈ L ↔ (γ.1 : Matrix (Fin n) (Fin n) E).mulVec x ∈ L := by
  have hfg : L.FG := Submodule.IsLattice.fg (A := E)
  have hfin : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hfg
  have hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤ := Submodule.IsLattice.span_eq_top
  have h1 := (mem_levelOpen_iff_latHat σ J hfg (ratEmb σ J γ)).1 hg (fun i => (1 : Af F) ⊗ₜ[F] x i)
  rw [mulVec_fv h] at h1
  have up : ∀ {z : Fin n → E}, z ∈ L →
      (fun i => (1 : Af F) ⊗ₜ[F] z i) ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) := fun {z} hz =>
    AddSubgroup.subset_closure ⟨1, fun v => by simp, z, hz, rfl⟩
  exact ⟨fun hx => Formalism.IndefR.CoreT.mem_of_latHat L hfin hsp (h1.1 (up hx)),
    fun hx => Formalism.IndefR.CoreT.mem_of_latHat L hfin hsp (h1.2 (up hx))⟩

theorem finite_level_rat (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hp : CompanionTheory.Rg.Fl.IsPosDef σ J)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] :
    {γ : GRat σ J | ratEmb σ J γ ∈ levelOpen σ J L}.Finite := by
  have hfg : L.FG := Submodule.IsLattice.fg (A := E)
  have hfin : Finite (Formalism.UG.level (σ : E →+* E) J L) := Formalism.UG.Final.StabFinite F E (Fin n) σ J
    (fun τ => RingHom.ext fun x => h.2.2.2 τ x) (by
      ext i j
      exact hJ.1 i j)
    (isUnit_iff_ne_zero.2 hJ.2) (isTotDef_of_posDef h hJ hp) L
    (Module.Finite.iff_fg.2 hfg) Submodule.IsLattice.span_eq_top
  let f : {γ : GRat σ J | ratEmb σ J γ ∈ levelOpen σ J L} → Formalism.UG.level (σ : E →+* E) J L :=
    fun γ => ⟨γ.1.1, γ.1.2, fun x => stab_of_mem_levelOpen h γ.2 x⟩
  have hf : Function.Injective f := fun a b e => Subtype.ext (Subtype.ext (congrArg (fun y : Formalism.UG.level (σ : E →+* E) J L => y.1) e))
  haveI := Finite.of_injective f hf
  exact Set.toFinite _

theorem exists_class_cover (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hp : CompanionTheory.Rg.Fl.IsPosDef σ J)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] :
    ∃ T : Finset (GAd σ J), ∀ x, ∃ (γ : GRat σ J), ∃ a ∈ T, ∃ k ∈ levelOpen σ J L, x = ratEmb σ J γ * a * k := by
  classical
  have hfg : L.FG := Submodule.IsLattice.fg (A := E)
  have hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤ := Submodule.IsLattice.span_eq_top
  letI := cmStarRing h
  let c : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext (sigma_invol h)) (AlgHom.ext (sigma_invol h))
  have hcs : ∀ x, c x = σ x := fun _ => rfl
  have hG : GlobalTheory.UnRep.IsHermForm c Jᵀ := by
    obtain ⟨z, hz⟩ := exists_sigma_ne h
    refine ⟨sigma_invol h, fun e => hz ?_, fun a b => hJ.1 a b, by rw [Matrix.det_transpose]; exact hJ.2⟩
    have := congrArg (fun d : E ≃ₐ[F] E => d z) e
    exact this
  have hsig : ∀ τ : E →+* ℂ, PI.UJClassFin.HasSignature (J.map τ) n 0 := fun τ => by
    have := CompanionTheory.Rg.FlCls.hasSignature c Jᵀ hG (fun τ x => h.2.2.2 τ x) τ (fun x hx => by
      have e := hp x hx τ
      have e2 : GlobalTheory.UnRep.hermE c Jᵀ x x = dotProduct (fun i => σ (x i)) (J.mulVec x) := by
        simp only [GlobalTheory.UnRep.hermE, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.transpose_apply, hcs]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e2]
      exact e)
    simpa using this
  obtain ⟨m, gs, hgs, -⟩ := unitary_class_set_finite F E σ n J (L : Set (Fin n → E)) (fun _ => rfl)
    (fun τ a => h.2.2.2 τ a) hsig (CompanionTheory.Rg.FlCls.exists_denom L hfg)
    (CompanionTheory.Rg.FlCls.exists_single_mem L hsp)
  refine ⟨Finset.univ.image gs, fun x => ?_⟩
  obtain ⟨i, γ, k, e⟩ := hgs x
  obtain ⟨δ, hδ, hδγ⟩ := γ.2
  refine ⟨⟨δ, hδ⟩, gs i, Finset.mem_image_of_mem _ (Finset.mem_univ i), k.1, ?_, ?_⟩
  · exact (mem_levelOpen_iff_latHat σ J hfg k.1).2 k.2
  · have : ratEmb σ J ⟨δ, hδ⟩ = γ.1 := Subtype.ext hδγ
    rw [this]
    exact e

theorem exists_cover_level {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsLattice E L] {W : Subgroup (GAd σ J)}
    (hW : IsOpen (W : Set (GAd σ J))) (hinf : ∀ y, ofInf σ J y ∈ W) :
    ∃ T : Finset (GAd σ J), ∀ k ∈ levelOpen σ J L, ∃ t ∈ T, ∃ w ∈ W, k = t * w := by
  obtain ⟨t, -, ht⟩ := (isCompact_levelFin σ J L).elim_nhds_subcover
    (fun c => (fun y => c⁻¹ * y) ⁻¹' (W : Set (GAd σ J)))
    (fun c _ => by
      have hc : Continuous fun y : GAd σ J => c⁻¹ * y := continuous_const.mul continuous_id
      exact hc.continuousAt.preimage_mem_nhds (hW.mem_nhds (by simp [one_mem])))
  refine ⟨t, fun k hk => ?_⟩
  have hf : ofFin σ J (projFin σ J k) ∈ ((levelFin σ J L : Subgroup (GAd σ J)) : Set (GAd σ J)) := by
    have e := image_ofFin_levelOffFin σ J L ∅
    exact e ▸ ⟨_, (mem_levelOpen_iff_projFin σ J L).1 hk, rfl⟩
  have h1 := ht hf
  simp only [Set.mem_iUnion, Set.mem_preimage] at h1
  obtain ⟨c, hc, hcy⟩ := h1
  refine ⟨c, hc, c⁻¹ * k, ?_, by group⟩
  have e : c⁻¹ * k = (c⁻¹ * ofFin σ J (projFin σ J k)) * ofInf σ J (projInf σ J k) := by
    have e0 := ofInf_projInf_mul_ofFin_projFin σ J k
    rw [(commute_ofInf_ofFin σ J _ _).eq] at e0
    rw [mul_assoc, e0]
  rw [e]
  exact mul_mem hcy (hinf _)

theorem mem_image_of_smul {G : Type} [Group G] {Γ K : Subgroup G} (γ : Γ) {x y : G ⧸ K} (e : γ • x = y) :
    (γ : G) ∈ (fun k => y.out * k * x.out⁻¹) '' (K : Set G) := by
  have h1 : (((γ : G) * x.out : G) : G ⧸ K) = ((y.out : G) : G ⧸ K) := by
    rw [QuotientGroup.out_eq']
    rw [← e]
    conv_rhs => rw [← QuotientGroup.out_eq' x]
    rfl
  refine ⟨y.out⁻¹ * ((γ : G) * x.out), (QuotientGroup.eq.1 h1.symm), by group⟩

theorem finite_orbits {v : HeightOneSpectrum (𝓞 F)} {K : Subgroup (GLoc σ J v)} {W : Subgroup (GAd σ J)}
    (hW : W ≤ K.comap (proj σ J v)) {T : Finset (GAd σ J)}
    (hT : ∀ x, ∃ (γ : GRat σ J), ∃ a ∈ T, ∃ w ∈ W, x = ratEmb σ J γ * a * w) :
    Finite (MulAction.orbitRel.Quotient (ratGroup σ J v W) (GLoc σ J v ⧸ K)) := by
  choose c a ha w hw e using hT
  let Φ : MulAction.orbitRel.Quotient (ratGroup σ J v W) (GLoc σ J v ⧸ K) → T :=
    fun q => ⟨a (emb σ J v (Quotient.out q).out), ha _⟩
  refine Finite.of_injective Φ fun q q' hq => ?_
  have h1 : a (emb σ J v (Quotient.out q).out) = a (emb σ J v (Quotient.out q').out) := congrArg Subtype.val hq
  have e' := e (emb σ J v (Quotient.out q').out)
  rw [← h1] at e'
  obtain ⟨x, hx, k, hk, hxk⟩ := mem_orbit_of_eq hW (hw _) (hw _) (e (emb σ J v (Quotient.out q).out)) e'
  have h2 : (⟨x, hx⟩ : ratGroup σ J v W) • (Quotient.out q) = Quotient.out q' := by
    conv_lhs => rw [← QuotientGroup.out_eq' (Quotient.out q)]
    conv_rhs => rw [← QuotientGroup.out_eq' (Quotient.out q')]
    show ((x * (Quotient.out q).out : GLoc σ J v) : GLoc σ J v ⧸ K) = _
    rw [hxk]
    exact QuotientGroup.mk_mul_of_mem _ hk
  rw [← Quotient.out_eq' q, ← Quotient.out_eq' q']
  have h3 : Quotient.out q' ∈ MulAction.orbit (ratGroup σ J v W) (Quotient.out q) := ⟨⟨x, hx⟩, h2⟩
  exact (Quotient.eq''.2 (MulAction.orbitRel_apply.2 h3)).symm

theorem isSep_of_posDef (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hp : CompanionTheory.Rg.Fl.IsPosDef σ J)
    (v : HeightOneSpectrum (𝓞 F)) (K : Subgroup (GLoc σ J v)) (hKo : IsOpen (K : Set (GLoc σ J v)))
    (hKc : IsCompact (K : Set (GLoc σ J v))) : CompanionTheory.Rg.Fl.IsSep K := by
  classical
  intro S
  haveI : Submodule.IsLattice E (stdLattice E n) := isLattice_stdLattice
  set L := stdLattice E n with hL
  have hB := finite_level_rat h hJ hp L
  obtain ⟨T₁, hT₁⟩ := exists_class_cover h hJ hp L
  set W₀ : Subgroup (GAd σ J) := levelOpen σ J L ⊓ K.comap (proj σ J v) with hW₀
  let C : Set (GLoc σ J v) := ⋃ x ∈ S, ⋃ y ∈ S, (fun k => y.out * k * x.out⁻¹) '' (K : Set (GLoc σ J v))
  have hC : IsCompact C := S.finite_toSet.isCompact_biUnion fun x _ =>
    S.finite_toSet.isCompact_biUnion fun y _ => hKc.image (by fun_prop)
  have hfin := finite_local hB hKc hC
  obtain ⟨u, hu⟩ : ∃ u : HeightOneSpectrum (𝓞 F), u ≠ v := by
    haveI := GlobalTheory.HTPlaceLeaf.infinite_places F
    exact exists_ne v
  let B : Set (GLoc σ J u) := ratLoc σ J u '' ({δ : GRat σ J | ratEmb σ J δ ∈ (emb σ J v).range ⊔ W₀ ∧
    ratLoc σ J v δ ∈ C} \ {1})
  have hBfin : B.Finite := (hfin.subset Set.diff_subset).image _
  have h1B : (1 : GLoc σ J u) ∉ B := by
    rintro ⟨δ, hδ, e⟩
    exact hδ.2 (ratLoc_injective σ J u (e.trans (map_one _).symm))
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GLoc σ J u
  obtain ⟨O, hO⟩ := NonarchimedeanGroup.is_nonarchimedean _ (hBfin.isClosed.isOpen_compl.mem_nhds h1B)
  set W : Subgroup (GAd σ J) := W₀ ⊓ (O : Subgroup (GLoc σ J u)).comap (proj σ J u) with hW
  have hWW₀ : W ≤ W₀ := inf_le_left
  have hWK : W ≤ K.comap (proj σ J v) := hWW₀.trans inf_le_right
  have hWo : IsOpen (W : Set (GAd σ J)) :=
    ((isOpen_levelOpen σ J L).inter (hKo.preimage (continuous_proj σ J v))).inter
      (O.isOpen.preimage (continuous_proj σ J u))
  have hinf : ∀ y, ofInf σ J y ∈ W := fun y =>
    ⟨⟨mem_levelOpen.2 fun t => by rw [proj_ofInf]; exact one_mem _, by
      show proj σ J v _ ∈ K
      rw [proj_ofInf]; exact one_mem _⟩, by
      show proj σ J u _ ∈ (O : Subgroup (GLoc σ J u))
      rw [proj_ofInf]; exact one_mem _⟩
  obtain ⟨T₂, hT₂⟩ := exists_cover_level (L := L) hWo hinf
  have hsup : (emb σ J v).range ⊔ W ≤ (emb σ J v).range ⊔ W₀ := sup_le_sup_left hWW₀ _
  refine ⟨ratGroup σ J v W, finite_orbits (T := Finset.image₂ (· * ·) T₁ T₂) hWK fun x => ?_, fun x => ?_,
    fun x hx y hy γ e => ?_⟩
  · obtain ⟨γ, a, ha, k, hk, rfl⟩ := hT₁ x
    obtain ⟨t, ht, w, hw, rfl⟩ := hT₂ k hk
    exact ⟨γ, a * t, Finset.mem_image₂_of_mem ha ht, w, hw, by simp only [mul_assoc]⟩
  · have hCx : IsCompact ((fun k => x.out * k * x.out⁻¹) '' (K : Set (GLoc σ J v))) := hKc.image (by fun_prop)
    have hD := finite_local hB hKc hCx
    haveI : Finite (ratLoc σ J v '' {δ : GRat σ J | ratEmb σ J δ ∈ (emb σ J v).range ⊔ (levelOpen σ J L ⊓
        K.comap (proj σ J v)) ∧ ratLoc σ J v δ ∈ (fun k => x.out * k * x.out⁻¹) '' (K : Set (GLoc σ J v))}) :=
      (hD.image _).to_subtype
    refine Finite.of_injective (β := ratLoc σ J v '' {δ : GRat σ J | ratEmb σ J δ ∈ (emb σ J v).range ⊔
      (levelOpen σ J L ⊓ K.comap (proj σ J v)) ∧ ratLoc σ J v δ ∈ (fun k => x.out * k * x.out⁻¹) ''
      (K : Set (GLoc σ J v))}) (fun s => ⟨(s.1 : GLoc σ J v), ?_⟩) ?_
    · obtain ⟨δ, hδ, e⟩ := s.1.2
      refine ⟨δ, ⟨hsup hδ, ?_⟩, e⟩
      rw [e]
      exact mem_image_of_smul s.1 (MulAction.mem_stabilizer_iff.1 s.2)
    · intro a b e
      have e' : ((a.1 : ratGroup σ J v W) : GLoc σ J v) = ((b.1 : ratGroup σ J v W) : GLoc σ J v) :=
        Subtype.mk.inj e
      exact Subtype.ext (Subtype.ext e')
  · obtain ⟨δ, hδ, eδ⟩ := γ.2
    by_cases h1 : δ = 1
    · have hγ : γ = 1 := Subtype.ext (by rw [← eδ, h1, map_one]; rfl)
      rw [← e, hγ, one_smul]
    · exfalso
      have hmC : ratLoc σ J v δ ∈ C := by
        rw [eδ]
        exact Set.mem_biUnion hx (Set.mem_biUnion hy (mem_image_of_smul γ e))
      have hmB : ratLoc σ J u δ ∈ B := ⟨δ, ⟨⟨hsup hδ, hmC⟩, h1⟩, rfl⟩
      obtain ⟨y', w, hw, e1⟩ := exists_of_mem_sup (show ratEmb σ J δ ∈ (emb σ J v).range ⊔ W from hδ)
      have e2 : ratLoc σ J u δ = proj σ J u w := by
        rw [← proj_ratEmb, e1, map_mul, proj_emb_ne σ J hu, one_mul]
      have hmO : ratLoc σ J u δ ∈ (O : Subgroup (GLoc σ J u)) := e2 ▸ hw.2
      exact hO hmO hmB

end CompanionTheory.Rg.FlSep

theorem CompanionTheory.Rg.FlSep.stSepDefB : CompanionTheory.Rg.Fl.StSepDef := by
  intro F E _ _ _ _ _ σ h n J hJ hp v K hKo hKc
  exact CompanionTheory.Rg.FlSep.isSep_of_posDef h hJ hp v K hKo hKc
