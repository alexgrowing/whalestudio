import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PinnedIntegrability
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct Topology ComplexOrder

namespace GlobalTheory.ThetaIntegrand

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_princ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (T : Finset (Pl E))
    (h1 : ∀ i j, (β⁻¹ * x * β).1 i j ∈ Formalism.L2.Herm.intAf F E)
    (h2 : ∀ i j, (β⁻¹ * x * β)⁻¹.1 i j ∈ Formalism.L2.Herm.intAf F E)
    (h3 : ∀ PP ∈ T, ∀ i j, ∃ z ∈ Formalism.L2.Herm.intAf F E,
      (β⁻¹ * x * β).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j = (Ideal.absNorm PP.asIdeal : ℕ) * z) :
    x ∈ St β ∧ ∀ PP ∈ T, redFn β PP x = 1 := by
  have hx : x = β * (β⁻¹ * x * β) * β⁻¹ := by group
  generalize β⁻¹ * x * β = m at h1 h2 h3 hx
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) =>
      A.map (Formalism.L2.Herm.intAf F E).subtype := Matrix.map_injective Subtype.val_injective
  let y : GL (Fin n) (Formalism.L2.Herm.intAf F E) :=
    ⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩,
      hi (by
        simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact m.mul_inv),
      hi (by
        simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact m.inv_mul)⟩
  have hy : frGL β y = x := by
    have : intGL F E n y = m := Units.ext rfl
    rw [hx, ← this]
    rfl
  refine ⟨⟨y, hy⟩, fun PP hP => ?_⟩
  rw [← hy, redFn_frGL]
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨z, hz, e⟩ := h3 PP hP i j
  have e1 : y.1 i j = (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j +
      (Ideal.absNorm PP.asIdeal : ℕ) * ⟨z, hz⟩ := by
    apply Subtype.ext
    have : (((1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j : Formalism.L2.Herm.intAf F E) :
        E ⊗[F] Formalism.L2.Herm.Af F) = (1 : Matrix (Fin n) (Fin n) _) i j := by
      simp only [Matrix.one_apply]; split_ifs <;> rfl
    rw [Subring.coe_add, Subring.coe_mul, Subring.coe_natCast, this, ← e, add_sub_cancel]
    rfl
  have e2 : ((Ideal.absNorm PP.asIdeal : ℕ) : kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.absNorm_mem _)
  change resS F PP (y.1 i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j
  rw [e1, map_add, map_mul, map_natCast, e2, zero_mul, add_zero]
  simp only [Matrix.one_apply]; split_ifs <;> simp

theorem eventually_princ_mat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Af F)) (T : Finset (Pl E)) {X : Type} [TopologicalSpace X] {x₀ : X}
    {φ : X → GL (Fin n) (Af F ⊗[F] E)} (hf : Continuous φ) (h₀ : φ x₀ = 1) :
    ∀ᶠ κ in 𝓝 x₀, Formalism.UG.bc (GlobalTheory.Mass.swapTens F E (Af F) : _ →+* _) (φ κ) ∈ St β ∧
      ∀ PP ∈ T, redFn β PP (Formalism.UG.bc (GlobalTheory.Mass.swapTens F E (Af F) : _ →+* _) (φ κ)) = 1 := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  have ho := (GlobalTheory.Mass.intTens_open_compact F E).1
  set s := GlobalTheory.Mass.swapTens F E (Af F)
  let β' : GL (Fin n) (Af F ⊗[F] E) := Formalism.UG.bc (s.symm : _ →+* _) β
  have hβ : Formalism.UG.bc (s : _ →+* _) β' = β := Units.ext (Matrix.ext fun i j => s.apply_symm_apply _)
  let m : X → GL (Fin n) (Af F ⊗[F] E) := fun κ => β'⁻¹ * φ κ * β'
  have hm : Continuous m := (continuous_const.mul hf).mul continuous_const
  have hm1 : m x₀ = 1 := by simp only [m, h₀, mul_one, inv_mul_cancel]
  have hs : ∀ κ, β⁻¹ * Formalism.UG.bc (s : _ →+* _) (φ κ) * β = Formalism.UG.bc (s : _ →+* _) (m κ) := fun κ => by
    simp only [m, map_mul, map_inv, hβ]
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j ∈
      GlobalTheory.Mass.intTens F E := fun i j => by
    simp only [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  have e1 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, (m κ).1 i j ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    exact (ho.preimage ((Units.continuous_val.comp hm).matrix_elem i j)).mem_nhds
      (show (m x₀).1 i j ∈ _ by rw [hm1]; exact hone i j)
  have e2 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, (m κ)⁻¹.1 i j ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    exact (ho.preimage ((Units.continuous_coe_inv.comp hm).matrix_elem i j)).mem_nhds
      (show (m x₀)⁻¹.1 i j ∈ _ by rw [hm1, inv_one]; exact hone i j)
  have e3 : ∀ᶠ κ in 𝓝 x₀, ∀ PP ∈ T, ∀ i j,
      algebraMap F _ ((Ideal.absNorm PP.asIdeal : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j) ∈ GlobalTheory.Mass.intTens F E := by
    rw [Filter.eventually_all_finset]
    simp only [Filter.eventually_all]
    intro PP _ i j
    have hc : Continuous fun κ => algebraMap F (Af F ⊗[F] E) ((Ideal.absNorm PP.asIdeal : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j) :=
      continuous_const.mul (((Units.continuous_val.comp hm).matrix_elem i j).sub continuous_const)
    refine (ho.preimage hc).mem_nhds ?_
    rw [Set.mem_preimage, hm1, Units.val_one, sub_self, mul_zero]
    exact (GlobalTheory.Mass.intTens F E).zero_mem
  filter_upwards [e1, e2, e3] with κ h1 h2 h3
  refine mem_princ β _ T ?_ ?_ ?_
  · rw [hs]; exact h1
  · rw [hs, ← map_inv]; exact h2
  · intro PP hP i j
    refine ⟨_, h3 PP hP i j, ?_⟩
    have hN : ((Ideal.absNorm PP.asIdeal : ℕ) : F) ≠ 0 :=
      Nat.cast_ne_zero.2 fun h0 => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    have e : (m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j =
        (Ideal.absNorm PP.asIdeal : ℕ) * (algebraMap F _ ((Ideal.absNorm PP.asIdeal : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j)) := by
      rw [← mul_assoc, ← map_natCast (algebraMap F (Af F ⊗[F] E)), ← map_mul,
        mul_inv_cancel₀ hN, map_one, one_mul]
    have := congrArg s e
    rw [map_mul, map_natCast, map_sub] at this
    rw [hs]
    refine Eq.trans ?_ this
    congr 1
    simp only [Matrix.one_apply]; split_ifs <;> simp

variable {D : D7}

theorem eventually_princ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (T : Finset (Pl D.host.E)) :
    ∀ᶠ κ in 𝓝 (1 : GA D V), finE V κ ∈ UA D.sp.cm V.gram ∧ finE V κ ∈ St β ∧ ∀ PP ∈ T, redFn β PP (finE V κ) = 1 := by
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have hf : Continuous (finHom V) :=
    (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
  filter_upwards [eventually_princ_mat β T hf (map_one _)] with κ h
  refine ⟨?_, h⟩
  have := (GlobalTheory.Mass.swapPts (Af D.host.F) D.sp.cm.sig V.gram (π κ)).2
  rwa [GlobalTheory.Mass.coe_swapPts, hπ κ] at this

theorem levFn_eq_one {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (L : LevDat D.host.E ℂ n)
    (hg : ∀ PP ∈ L.Pg, redFn β PP x = 1) (hq : ∀ PP ∈ L.Q, redFn β PP x = 1) : levFn β L x = 1 := by
  have h1 : rTup β L x = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 x) = 1
    rw [hg PP.1 PP.2]; exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levFn
  rw [h1, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hP
    rw [hq PP hP, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [hg PP hP, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]

section Generic

variable {G H W : Type} [Group G] [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : G →* H) (Γ : Subgroup G)
  (ρ : G →* Module.End ℂ W) {J : Subgroup H} {χ : J →* ℂˣ} {f : H → W}

theorem form_invariant (hf : f ∈ Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    ρ (γ * g)⁻¹ (f (π (γ * g))) = ρ g⁻¹ (f (π g)) := by
  have h := hf ⟨γ, hγ⟩ (π g) 1
  rw [map_one, Units.val_one, one_smul, OneMemClass.coe_one, mul_one] at h
  have h' : f (π (γ * g)) = ρ γ (f (π g)) := by rw [map_mul]; exact h
  rw [h', ← Module.End.mul_apply, ← map_mul, _root_.mul_inv_rev, inv_mul_cancel_right]

theorem form_continuous [TopologicalSpace G] [IsTopologicalGroup G] (hρ : ∀ x, Continuous fun g => ρ g x)
    (hJ : ∀ᶠ κ in 𝓝 (1 : G), ∃ h : π κ ∈ J, χ ⟨_, h⟩ = 1)
    (hf : f ∈ Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ) : Continuous fun g => ρ g⁻¹ (f (π g)) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have h0 : Continuous fun h : G => ρ h⁻¹ (f (π g)) := (hρ _).comp continuous_inv
  refine h0.continuousAt.congr ?_
  have ht : Filter.Tendsto (fun h : G => g⁻¹ * h) (𝓝 g) (𝓝 1) := by
    simpa using (continuous_const_mul g⁻¹).tendsto g
  filter_upwards [ht.eventually hJ] with h hh
  obtain ⟨hk, h5⟩ := hh
  have h4 := hf 1 (π g) ⟨_, hk⟩
  rw [h5, map_one, map_one, Units.val_one, one_smul, one_mul, ← map_mul, mul_inv_cancel_left] at h4
  rw [h4]
  rfl

end Generic

theorem eventually_level (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∀ᶠ κ in 𝓝 (1 : GA D V), ∃ h : (finHom V).rangeRestrict κ ∈ (levEnv V β L).J, (levEnv V β L).χ ⟨_, h⟩ = 1 := by
  classical
  filter_upwards [eventually_princ V β (L.Pg ∪ L.Q)] with κ hh
  obtain ⟨h1, h2, h3⟩ := hh
  have hk : finE V κ ∈ lev D.sp.cm V.gram β (flag1L L) :=
    Kg_le_lev (D := flag1L L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right
      ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩
  exact ⟨hk, levFn_eq_one β (finE V κ) (flag1L L) (fun PP hP => h3 PP (Finset.mem_union_left _ hP))
    fun PP hP => h3 PP (Finset.mem_union_right _ hP)⟩

theorem ext_invariant {V : HSp D} (c : CoefA V) {J : Subgroup (Bridge.Gf V)} {χ : J →* ℂˣ} {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ J χ) : ∀ γ ∈ GQ V, ∀ g, c.ext f (γ * g) = c.ext f g :=
  fun _ hγ g => form_invariant (finHom V).rangeRestrict (GQ V) c.ρ hf hγ g

theorem ext_continuous {V : HSp D} (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ) : Continuous (c.ext f) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  exact form_continuous (finHom V).rangeRestrict (GQ V) c.ρ hc.2.2.1 (eventually_level V β L) hf

theorem integrableOn_form {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hs : S.SigOK)
    (hp : S.IsPosDef) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank)
    {f : Bridge.Gf S → c.W} (hf : f ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J (levEnv S β L).χ)
    (pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ P, IsThetaFunO ψ S T (pt P))
    (io : c.W →ₗ[ℂ] PolF D T.rank S.rank) {K : Subgroup (GL (Fin S.rank) (Lev.EAf D))} {μ : Measure (GA D S)}
    {𝓕 : Set (GA D S)} (hμ : IsMeasDef S K μ 𝓕) (g : GA D T) :
    IntegrableOn (fun h => thetaKO om h g (pt (io (c.ext f h)))) 𝓕 μ := by
  have hpos : ∀ τ, (gramAt D S τ).PosDef := fun τ => by
    have := hs (tauE D τ)
    rw [hp] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  exact GlobalTheory.DefiniteQuotient.integrableOn_theta D ψ hom.std S T χS χT om hom hpos c.W (pt ∘ₗ io)
    (fun w => hpt _) _ (ext_continuous c hc β L hf) (ext_invariant c hf) μ 𝓕 hμ.1.1 hμ.2 g

theorem thetaIntegrandIntegrable : GlobalTheory.IndefiniteRowSideFullHecke.PinnedIntegrability.ThetaIntegrandIntegrable := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hR i t f hf e g
  obtain ⟨x, hf⟩ := hf
  have hx : (R.HV i t).e x ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ :=
    (hR.HV i t).2.1.le (LinearMap.mem_range_self _ x)
  have hf' : f = (R.cV i).ext ((R.HV i t).e x) := hf.symm
  have key := integrableOn_form (hR.ωP i t) (D.sp.V_sig _) (hR.vpos i) (R.cV i) (hR.cV i) (R.βV i) (R.datVt i t) hx
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t)) (hR.pt_theta i t) (R.ioP i e) (hR.νV i t) g
  rw [← hf'] at key
  exact key

end GlobalTheory.ThetaIntegrand

end
