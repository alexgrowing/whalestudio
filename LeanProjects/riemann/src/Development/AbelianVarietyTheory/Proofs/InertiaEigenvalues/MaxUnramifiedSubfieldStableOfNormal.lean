import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallyCrystallineModuleEqCrystallineRestric
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial
open Classical

noncomputable section

namespace GlobalTheory.PotExt

variable {l : ℕ} [Fact l.Prime]

section Bridge

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

theorem exists_finExt_of_open (U : Subgroup (Ω ≃ₐ[E] Ω)) (hU : IsOpen (U : Set (Ω ≃ₐ[E] Ω))) :
    ∃ L : FinExt l, ∀ g : ↥(GK Bw.Kw), (g : GQ l) ∈ GK L → ((Bw.e.symm g : Gw) : Ω ≃ₐ[E] Ω) ∈ U := by
  have hc : Continuous fun g : ↥(GK Bw.Kw) => ((Bw.e.symm g : Gw) : Ω ≃ₐ[E] Ω) :=
    continuous_subtype_val.comp Bw.e_symm_cont
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.1 (hU.preimage hc)
  have h1 : (1 : GQ l) ∈ t := by
    have : (1 : ↥(GK Bw.Kw)) ∈ Subtype.val ⁻¹' t := by
      rw [hts]
      simp [U.one_mem]
    exact this
  obtain ⟨L, hL, hLt⟩ := (krullTopology_mem_nhds_one_iff ℚ_[l] (Om l) t).1 (ht.mem_nhds h1)
  refine ⟨⟨L, hL⟩, fun g hg => ?_⟩
  have : g ∈ Subtype.val ⁻¹' t := hLt hg
  rw [hts] at this
  exact this

theorem rep_apply {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O) (g : ↥(GK Bw.Kw))
    (x : Fin m → ↥Bw.LL.1) :
    Bw.rep r g x = (((r (Bw.e.symm g) : Matrix.GeneralLinearGroup (Fin m) O) : Matrix (Fin m) (Fin m) O).map Bw.toLL).mulVec x := rfl

end Bridge

end GlobalTheory.PotExt

namespace GlobalTheory.PotExt

variable {l : ℕ} [Fact l.Prime]

section Lat

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

theorem toLL_mem (a : O) : Bw.toLL a ∈ OL Bw.LL := (Bw.eO a).2

theorem mem_stdG_OL {LL : FinExt l} {k : ℕ} (x : Fin k → ↥LL.1) :
    x ∈ stdG ↥(OL LL) ↥LL.1 k ↔ ∀ j, x j ∈ OL LL := by
  constructor
  · rintro ⟨u, rfl⟩ j
    exact (u j).2
  · intro h
    exact ⟨fun j => ⟨x j, h j⟩, rfl⟩

set_option synthInstance.maxHeartbeats 400000 in

def bridgeLat {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O)
    (hr : Continuous fun g => ((r g : Matrix.GeneralLinearGroup (Fin m) O) : Matrix (Fin m) (Fin m) O))
    {K : FinExt l} (h : Bw.Kw.1 ≤ K.1) : LocLat ↥(GK K) ℚ_[l] ↥Bw.LL.1 ↥(OL Bw.LL) where
  V := Fin m → ↥Bw.LL.1
  ρ := (Bw.rep r).comp (Subgroup.inclusion (GK_le h))
  cont := fun x => by
    have h1 : Continuous fun g : ↥(GK K) =>
        ((r (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) : Matrix.GeneralLinearGroup (Fin m) O) :
          Matrix (Fin m) (Fin m) O) :=
      hr.comp (Bw.e_symm_cont.comp (continuous_subtype_val.subtype_mk _))
    have h2 : Continuous (Bw.toLL) := continuous_subtype_val.comp Bw.eO_cont
    exact (h1.matrix_map h2).matrix_mulVec continuous_const
  L :=
    { T := stdG ↥(OL Bw.LL) ↥Bw.LL.1 m
      stable := fun g x hx => by
        rw [mem_stdG_OL] at hx ⊢
        intro j
        simp only [MonoidHom.comp_apply, GlobalTheory.PotExt.rep_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
        exact Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (toLL_mem Bw _) (hx b)
      fg := by
        rw [stdG, LinearMap.range_eq_map]
        exact (Module.Finite.fg_top).map _
      free := Module.Free.of_equiv (LinearEquiv.ofInjective _ (stdG_inj Subtype.val_injective m))
      span := by
        rw [eq_top_iff, ← (Pi.basisFun ↥Bw.LL.1 (Fin m)).span_eq]
        apply Submodule.span_mono
        rintro _ ⟨j, rfl⟩
        refine ⟨Pi.single j 1, ?_⟩
        funext j'
        simp [Pi.single_apply] }

theorem isCrys_up (LT : LocTheory) (hres : ElementDenominator.CrystallineRestrictionToExtension LT) {m : ℕ}
    (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O)
    (hr : Continuous fun g => ((r g : Matrix.GeneralLinearGroup (Fin m) O) : Matrix (Fin m) (Fin m) O))
    {K₁ K₂ : FinExt l} (h₁ : Bw.Kw.1 ≤ K₁.1) (h₁₂ : K₁.1 ≤ K₂.1)
    (hc : IsCrys ((LT l).PD K₁) ((Bw.rep r).comp (Subgroup.inclusion (GK_le h₁)))) :
    IsCrys ((LT l).PD K₂) ((Bw.rep r).comp (Subgroup.inclusion (GK_le (h₁.trans h₁₂)))) :=
  (hres l K₂ K₁ h₁₂ (GK_le h₁₂) Bw.LL (bridgeLat Bw r hr h₁) hc).1

end Lat

end GlobalTheory.PotExt

namespace GlobalTheory.PotExt

variable {l : ℕ} [Fact l.Prime]

theorem Kur_stable (σ : GQ l) {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) : σ x ∈ MaximalUnramifiedExtension l := by
  have h : (MaximalUnramifiedExtension l).map (σ : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    rw [IntermediateField.adjoin_map]
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, ⟨m, hm, hlm, hy⟩, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, by rw [← map_pow, hy, map_one]⟩
  exact h ((IntermediateField.mem_map _).2 ⟨x, hx, rfl⟩)

theorem mem_of_normal {K' : FinExt l} (hn : Normal ℚ_[l] K'.1) (σ : GQ l) {x : Om l} (hx : x ∈ K'.1) :
    σ x ∈ K'.1 :=
  IntermediateField.normal_iff_forall_map_le'.1 hn σ ((IntermediateField.mem_map _).2 ⟨x, hx, rfl⟩)

theorem GKin_normal {K K' : FinExt l} (h : K.1 ≤ K'.1) (hn : Normal ℚ_[l] K'.1) : (GKin h).Normal := by
  haveI : IsGalois ℚ_[l] K'.1 := IsGalois.mk
  haveI : (GK K').Normal := (InfiniteGalois.normal_iff_isGalois K'.1).2 inferInstance
  unfold GKin
  infer_instance

theorem GKin_finiteIndex {K K' : FinExt l} (h : K.1 ≤ K'.1) : (GKin h).FiniteIndex := by
  haveI : Finite (GQ l ⧸ GK K') := Subgroup.quotient_finite_of_isOpen _ (@IntermediateField.fixingSubgroup_isOpen _ _ _ _ _ K'.1 K'.2)
  haveI : (GK K').FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  unfold GKin
  infer_instance

theorem maxUnramifiedSubfield_stable_of_normal (P : LocPrime l) {K K' : FinExt l} (hn : Normal ℚ_[l] K'.1) (g : ↥(GK K)) (c : ↥(K0 K')) :
    ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c' := by
  have hc1 : ((c : Om l)) ∈ K'.1 := c.2.1
  have hc2 : ((c : Om l)) ∈ MaximalUnramifiedExtension l := c.2.2
  refine ⟨⟨(g : GQ l) c, mem_of_normal hn _ hc1, Kur_stable _ hc2⟩, ?_⟩
  rw [P.PD_actB]
  exact P.actQ_Kur (g : GQ l) ⟨c, hc2⟩ ⟨(g : GQ l) c, Kur_stable _ hc2⟩ rfl

end GlobalTheory.PotExt

namespace GlobalTheory.PotExt

theorem main : ∀ (D : D7) (P : Pend D), ElementDenominator.adm12 D → ∀ (i : D.nd.Loc) (k : Fin 2)
  (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
  (Y : Finset (Fb (D.host.g k) (D.host.g_prime k))), (∀ y ∈ Y, y ≠ 0) →
  ∀ (ι : Type) [Finite ι] (n : ℕ) (R : ι → (GE D.nd →* GL (Fin n) (D.nd.O i))) (n₀ : ℕ)
    (R₀ : GE D.nd →* GL (Fin n₀) (D.nd.O i)),
  (∀ j, Continuous fun g => ((R j g : GL (Fin n) (D.nd.O i)) : Matrix (Fin n) (Fin n) (D.nd.O i))) →
  (Continuous fun g => ((R₀ g : GL (Fin n₀) (D.nd.O i)) : Matrix (Fin n₀) (Fin n₀) (D.nd.O i))) →
  (∀ j, Br.IsPotCrysW D.loc D.nbr i w hw (R j)) → Br.IsPotCrysW D.loc D.nbr i w hw R₀ →
  ∃ (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
      (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
        ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
          algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c'),
    (∀ j, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((R j).comp (decS D.nd w)))) ∧
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (R₀.comp (decS D.nd w))) ∧
    ∀ y ∈ Y, ∀ g ∈ GKin h,
      (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) →
        P.om k w y (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) = 1 := by
  intro D P hadm i k w hw Y hY ι _ n R n₀ R₀ hRc hR₀c hRp hR₀p
  unfold Br.IsPotCrysW LocBridge.IsPotCrysW at hRp hR₀p
  choose Kj hj hcj using hRp
  obtain ⟨K₀', h₀, hc₀⟩ := hR₀p
  have hLy : ∀ y : ↥Y, ∃ L : FinExt (D.nd.l i), ∀ g : ↥(GK (D.nbr i w hw).Kw), (g : GQ (D.nd.l i)) ∈ GK L →
      (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) →
      P.om k w y (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) = 1 := by
    intro y
    obtain ⟨U, hU, hUo⟩ := P.om_open k w y (hY y y.2)
    obtain ⟨L, hL⟩ := exists_finExt_of_open (D.nbr i w hw) U hU
    exact ⟨L, fun g hg hI => hUo _ (hL g hg) hI⟩
  choose Ly hLy using hLy
  haveI : ∀ j, FiniteDimensional ℚ_[D.nd.l i] (Kj j).1 := fun j => (Kj j).2
  haveI : ∀ y, FiniteDimensional ℚ_[D.nd.l i] (Ly y).1 := fun y => (Ly y).2
  haveI := (D.nbr i w hw).Kw.2
  haveI := K₀'.2
  let M : IntermediateField ℚ_[D.nd.l i] (Om (D.nd.l i)) :=
    (D.nbr i w hw).Kw.1 ⊔ K₀'.1 ⊔ (⨆ j, (Kj j).1) ⊔ (⨆ y, (Ly y).1)
  haveI : FiniteDimensional ℚ_[D.nd.l i] M := by infer_instance
  let K' : FinExt (D.nd.l i) := ⟨IntermediateField.normalClosure ℚ_[D.nd.l i] M (Om (D.nd.l i)), inferInstance⟩
  have hMK : M ≤ K'.1 := IntermediateField.le_normalClosure M
  have hn : Normal ℚ_[D.nd.l i] K'.1 := normalClosure.normal _ _ _
  have h : (D.nbr i w hw).Kw.1 ≤ K'.1 := le_trans (le_sup_left.trans (le_sup_left.trans le_sup_left)) hMK
  have h0K : K₀'.1 ≤ K'.1 := le_trans (le_sup_right.trans (le_sup_left.trans le_sup_left)) hMK
  refine ⟨K', h, GKin_normal h hn, GKin_finiteIndex h, maxUnramifiedSubfield_stable_of_normal _ hn, fun j => ?_, ?_, ?_⟩
  · have hjK : (Kj j).1 ≤ K'.1 :=
      le_trans ((le_iSup (fun j => (Kj j).1) j).trans (le_sup_right.trans le_sup_left)) hMK
    refine (GlobalTheory.PcRes.main _ _ _ _ _ h _ _ _ _ _).2.2 ?_
    exact isCrys_up (D.nbr i w hw) D.loc hadm _ ((hRc j).comp continuous_subtype_val) (hj j) hjK (hcj j)
  · refine (GlobalTheory.PcRes.main _ _ _ _ _ h _ _ _ _ _).2.2 ?_
    exact isCrys_up (D.nbr i w hw) D.loc hadm _ (hR₀c.comp continuous_subtype_val) h₀ h0K hc₀
  · intro y hy g hg hI
    have hyK : (Ly ⟨y, hy⟩).1 ≤ K'.1 :=
      le_trans ((le_iSup (fun y => (Ly y).1) ⟨y, hy⟩).trans le_sup_right) hMK
    exact hLy ⟨y, hy⟩ g (GK_le hyK (Subgroup.mem_subgroupOf.1 hg)) hI

end GlobalTheory.PotExt
