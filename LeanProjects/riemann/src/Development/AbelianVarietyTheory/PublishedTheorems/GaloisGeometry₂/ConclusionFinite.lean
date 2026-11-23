import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HeckeLAdicParameterAbove
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdPstCycRepNeTrivWD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne Polynomial TensorProduct Module

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published.ParamAboveModel

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw)

theorem eq_lpOfChar (x : WD h) (hx : x.lpDim = 1) (ξ : Weil h →* ℂˣ) (hξ : WeilDeligne.IsSmooth ξ)
    (he : ∀ σ, (ξ σ : ℂ) ∈ x.eig σ) : x = WD.lpOfChar h ξ hξ := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  obtain rfl : n = 1 := by simpa using hx
  have h1 : ∀ (f : End ℂ (Fin 1 → ℂ)) (c : ℂ), f.HasEigenvalue c → ∀ v, f v = c • v := by
    intro f c hc v
    obtain ⟨u, hu⟩ := hc.exists_hasEigenvector
    obtain ⟨d, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (K := ℂ) u hu.2).mp (by simp) v
    rw [map_smul, hu.apply_eq_smul, smul_comm]
  refine WD.sound ⟨LinearEquiv.refl ℂ _, fun σ v => ?_, fun v => ?_⟩
  · have h2 := he σ
    rw [WD.eig_mk, mem_roots (LinearMap.charpoly_monic _).ne_zero, ← End.hasEigenvalue_iff_isRoot_charpoly] at h2
    ext i
    simp [h1 _ _ h2 v]
  · obtain ⟨c, hc⟩ := End.exists_eigenvalue b.N
    have h0 : c = 0 := by
      obtain ⟨k, hk⟩ := b.nilpotent
      have := hc.pow k
      rw [hk] at this
      obtain ⟨u, hu⟩ := this.exists_hasEigenvector
      have h3 := hu.apply_eq_smul
      rw [LinearMap.zero_apply, eq_comm, smul_eq_zero] at h3
      exact (pow_eq_zero_iff'.mp (h3.resolve_right hu.2)).1
    have := h1 _ _ hc v
    rw [h0, zero_smul] at this
    simp [this]

theorem mem_eig_wdPst {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) (x : ↥(Dpst P ρ))
    [FiniteDimensional ↥LL.1 V] (h1 : finrank ↥LL.1 V = 1) (hV : IsPst P ρ) (hv : wdMk P ι ρ x ≠ 0)
    (σ : Weil h) (s : ↥LL.1) (hs : haveI := hV.finite; weilD Bw h P ρ σ x = s • x) :
    ι (s : Om l) ∈ (wdPst P ι Bw h hj ρ).eig σ := by
  have := hV.finite
  have hd : finrank ℂ (WDSpace P ι ρ) = 1 := by
    rw [LetterDim.finrank_wdSpace l P ι _ LL _ _ hV, h1]
  obtain ⟨u, -, hk, -, -, hu⟩ := wdRep_spec P ι Bw h hj ρ
  have huv := Test.apply_eq_of_nilpotent hd hv _ hk
  have hu1 : u = 1 := by
    refine Units.ext (LinearMap.ext fun y => ?_)
    obtain ⟨d, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (K := ℂ) _ hv).mp hd y
    rw [map_smul, huv]; rfl
  have he : (wdRep P ι Bw h hj ρ).ρ σ (wdMk P ι ρ x) = ι (s : Om l) • wdMk P ι ρ x := by
    have h1 := LinearMap.congr_fun (hu σ) (wdMk P ι ρ x)
    rw [hu1, one_zpow, Units.val_one, mul_one] at h1
    rw [← h1, wdRho_mk, hs, wdMk_smul]
  rw [wdPst_of_isPst ι Bw h hj hV, WD.eig_mk, mem_roots (LinearMap.charpoly_monic _).ne_zero,
    ← End.hasEigenvalue_iff_isRoot_charpoly]
  exact End.hasEigenvalue_of_hasEigenvector ⟨End.mem_eigenspace_iff.mpr he, hv⟩

omit [IsAlgClosure E Ω] in

theorem smooth_loc (χ : HChar E) : GlobalTheory.SmGL.IsSmoothChar (χ.loc w) := by
  obtain ⟨n, hn⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ w
  have hu := unif_spec w
  set c : w.adicCompletion E := ((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) ^ (n + 1) with hc
  have hv : Valued.v c = WithZero.exp (-((n : ℤ) + 1)) := by
    unfold IsUnifAt at hu
    rw [hc, map_pow, hu, ← WithZero.exp_nsmul]; congr 1; simp
  have ho : IsOpen {x : (w.adicCompletion E)ˣ | ((x : w.adicCompletion E) - 1) * c⁻¹ ∈ w.adicCompletionIntegers E} :=
    (Valued.isOpen_valuationSubring _).preimage ((Units.continuous_val.sub continuous_const).mul continuous_const)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (ho.mem_nhds (by simp)) fun x hx => ?_)
  have h1 : Valued.v (((x : w.adicCompletion E) - 1) * c⁻¹) ≤ 1 := hx
  rw [map_mul, map_inv₀, hv, mul_inv_le_iff₀ WithZero.exp_pos, one_mul] at h1
  have h2 : Valued.v ((x : w.adicCompletion E) - 1) < 1 :=
    h1.trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  refine hn x ?_ (h1.trans (WithZero.exp_le_exp.2 (by omega)))
  have := Valuation.map_one_add_of_lt _ h2
  rwa [add_sub_cancel] at this

theorem zpow_apply_eig {F M : Type} [Field F] [AddCommGroup M] [Module F M] (u : (End F M)ˣ) (x : M) (c : F)
    (hc : c ≠ 0) (hx : (u : End F M) x = c • x) (n : ℤ) : ((u ^ n : (End F M)ˣ) : End F M) x = c ^ n • x := by
  have hi : ((u⁻¹ : (End F M)ˣ) : End F M) x = c⁻¹ • x := by
    rw [eq_inv_smul_iff₀ hc, ← map_smul, ← hx, ← End.mul_apply, Units.inv_mul, End.one_apply]
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, Units.val_mul, End.mul_apply, hx, map_smul, ih, smul_smul,
      zpow_add_one₀ hc, mul_comm]
  | pred n ih => rw [zpow_sub_one, Units.val_mul, End.mul_apply, hi, map_smul, ih, smul_smul,
      zpow_sub_one₀ hc, mul_comm]

theorem mem_eig_of_period {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) (x : ↥(Dpst P ρ))
    [FiniteDimensional ↥LL.1 V] (h1 : finrank ↥LL.1 V = 1) (hV : IsPst P ρ) (hx0 : x ≠ 0) (c : ↥LL.1) (hc : c ≠ 0)
    (hx1 : phiD P ρ x = c • x) (σ : Weil h) (s : ↥LL.1) (hs : actD P ρ (weilToGK Bw h σ) x = s • x) :
    ι ((c ^ (-alpha l σ) * s : ↥LL.1) : Om l) ∈ (wdPst P ι Bw h hj ρ).eig σ := by
  have hfin := hV.finite
  have hxn : ∀ n : ℕ, (phiD P ρ ^ n) x = c ^ n • x := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', End.mul_apply, ih, map_smul, hx1, smul_smul, pow_succ]
  have hxz := zpow_apply_eig (phiU P ρ) x c hc hx1
  have hv : wdMk P ι ρ x ≠ 0 := fun h0 => hx0
    (GlobalTheory.PstFaithful.eq_zero_of_wdMk_phiD_pow l P ι _ LL _ _ _ fun n => by rw [hxn, wdMk_smul, h0, smul_zero])
  exact mem_eig_wdPst P ι Bw h hj ρ x h1 hV hv σ _ (by
    rw [weilD_apply, End.mul_apply, hxz, map_smul, hs, mul_smul])

omit [IsAlgClosure E Ω] in

theorem eq_loc {χ : HChar E} {ξ : (w.adicCompletion E)ˣ →* ℂˣ} (hξ : GlobalTheory.NPin.IsComp χ w ξ) : ξ = χ.loc w := by
  have hs := hξ.1.mul (smooth_loc (w := w) χ).inv
  have hc := Subgroup.isClosed_of_isOpen _ hs
  refine mul_inv_eq_one.1 (MonoidHom.ext fun y => ?_)
  by_contra hy
  obtain ⟨U, hU, hU'⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hc.isOpen_compl
  have hyU : (y : w.adicCompletion E) ∈ U := by
    have : y ∈ Units.val ⁻¹' U := by rw [hU']; exact hy
    exact this
  obtain ⟨k, hk1, hk2⟩ := (HeightOneSpectrum.denseRange_algebraMap E w).exists_mem_open
    (hU.inter isOpen_ne (t := {z | z ≠ 0})) ⟨y, hyU, y.ne_zero⟩
  have hk0 : k ≠ 0 := fun e => hk2 (by rw [e, map_zero])
  have h3 : Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom (Units.mk0 k hk0) ∈ Units.val ⁻¹' U := hk1
  rw [hU'] at h3
  refine h3 ?_
  show ξ _ * (χ.loc w _)⁻¹ = 1
  rw [hξ.2]
  exact mul_inv_cancel _

omit [IsAlgClosure E Ω] in

theorem isComp_loc (χ : HChar E) : GlobalTheory.NPin.IsComp χ w (χ.loc w) :=
  ⟨smooth_loc (w := w) χ, fun _ => rfl⟩

theorem rhs_eq {χ : HChar E} {ξ : (w.adicCompletion E)ˣ →* ℂˣ} (hξ : GlobalTheory.NPin.IsComp χ w ξ) {rc} (H : IsRec h rc) :
    ∃ (a : Weil h →* (w.adicCompletion E)ˣ) (_ : IsLocalArtin h a) (hs : WeilDeligne.IsSmooth ((χ.loc w).comp a)),
      rc (cls (GlobalTheory.SplitRead.Irr.ofDet 1 ξ hξ.1).toIrrRep) = WD.lpOfChar h ((χ.loc w).comp a) hs := by
  obtain rfl := eq_loc hξ
  obtain ⟨a, ha, ε, -, H⟩ := H
  exact ⟨a, ha, ha.smooth hξ.1, H.one _ hξ.1⟩

theorem mem_eig_wdAt (μ : G E Ω →* (Om l)ˣ) (hr : IsPstAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype))
    (b : P.R.B) (hb : b ≠ 0) (c : ℚ_[l]) (hc : c ≠ 0) (hφ : P.φB b = c • b) (κ : GQ l → ℚ_[l]) (hκ0 : ∀ g, κ g ≠ 0)
    (hκ : ∀ g, κ g • P.actQ g b = b) (K' : FinExt l)
    (hK : ∀ g : Dec (F := E) A, (Bw.e g : GQ l) ∈ GK K' → (μ g : Om l) = algebraMap _ _ (κ (Bw.e g)))
    (σ : Weil h) :
    ι ((μ σ : Om l) * algebraMap _ _ ((κ (weilToGK Bw h σ))⁻¹ * c ^ (-alpha l σ))) ∈
      (wdAt P ι Bw h hj ((rk1 μ).comp (Dec (F := E) A).subtype)).eig σ := by
  obtain ⟨L, r', hM, hV, e⟩ := wdAt_of_isPstAt ι Bw h hj hr
  rw [e]
  have hfin := hV.finite
  let m : Dec (F := E) A → ↥L.1 := fun g => (r' g : Matrix (Fin 1) (Fin 1) ↥L.1) 0 0
  have hm : ∀ g, (m g : Om l) = μ g := fun g => by
    have := congrArg (fun f : ↥(Dec (F := E) A) →* GL (Fin 1) (Om l) => (f g : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) hM.2
    simpa [Formalism.MainNotions.N.mapRep, rk1] using this
  have hρ : ∀ g v, Bw.repE L r' g v = m (Bw.e.symm g) • v := fun g v => by
    ext i
    fin_cases i
    simp [LocBridge.repE, m, Matrix.mulVec, dotProduct]
  let v0 : Fin 1 → ↥L.1 := fun _ => 1
  have hact : ∀ g, stRep P (Bw.repE L r') g (v0 ⊗ₜ[ℚ_[l]] (C b : Bst P)) =
      (m (Bw.e.symm g) * algebraMap ℚ_[l] _ (κ g)⁻¹) • (v0 ⊗ₜ[ℚ_[l]] (C b : Bst P)) := fun g => by
    have h1 : P.actQ g b = (κ g)⁻¹ • b := by rw [eq_inv_smul_iff₀ (hκ0 _), hκ]
    rw [stRep_tmul, hρ, actSt_C, h1, ← smul_C, tmul_smul, mul_comm, mul_smul, algebraMap_smul, smul_tmul']
    rfl
  have hmem : v0 ⊗ₜ[ℚ_[l]] (C b : Bst P) ∈ Dpst P (Bw.repE L r') := (mem_Dpst P _).mpr ⟨K', fun g hg => by
    have h2 : m (Bw.e.symm g) = algebraMap ℚ_[l] _ (κ g) := Subtype.ext (by
      rw [hm, hK _ (by simpa using hg)]; simp)
    rw [hact, h2, ← map_mul, mul_inv_cancel₀ (hκ0 _), map_one, one_smul]⟩
  let x : ↥(Dpst P (Bw.repE L r')) := ⟨_, hmem⟩
  let c' : ↥L.1 := algebraMap ℚ_[l] _ c
  have hc' : c' ≠ 0 := (_root_.map_ne_zero _).mpr hc
  have hx1 : phiD P _ x = c' • x := Subtype.ext (by
    show phiV P _ _ (v0 ⊗ₜ[ℚ_[l]] (C b : Bst P)) = c' • (v0 ⊗ₜ[ℚ_[l]] (C b : Bst P))
    rw [phiV_tmul, phiSt_C, hφ, ← smul_C, tmul_smul, algebraMap_smul])
  have hx0 : x ≠ 0 := fun h0 => by
    have h1 : v0 ⊗ₜ[ℚ_[l]] (C b : Bst P) = 0 := congrArg Subtype.val h0
    have h2 : Function.Injective (Algebra.TensorProduct.includeRight : Bst P →ₐ[ℚ_[l]] ↥L.1 ⊗[ℚ_[l]] Bst P) :=
      Algebra.TensorProduct.includeRight_injective (algebraMap ℚ_[l] ↥L.1).injective
    have h3 := congrArg (LinearMap.rTensor (Bst P) (LinearMap.proj (R := ℚ_[l]) (φ := fun _ : Fin 1 => ↥L.1) 0)) h1
    rw [LinearMap.rTensor_tmul, map_zero] at h3
    exact hb (C_eq_zero.mp (h2 (by rw [map_zero]; exact h3)))
  have key := mem_eig_of_period P ι Bw h hj (Bw.repE L r') x (by simp) hV hx0 c' hc' hx1 σ _
    (Subtype.ext (hact (weilToGK Bw h σ)))
  convert key using 2
  have e3 : ((Bw.e.symm (weilToGK Bw h σ) : Dec (F := E) A) : G E Ω) = σ := by simp [weilToGK]
  have e4 : ∀ z : ℚ_[l], ((algebraMap ℚ_[l] ↥L.1 z : ↥L.1) : Om l) = algebraMap _ _ z := fun _ => rfl
  rw [MulMemClass.coe_mul, MulMemClass.coe_mul, hm, e3, ← map_zpow₀, e4, e4, map_mul]
  ring

theorem conclusion_finite {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) {χ : HChar E} {k : ℕ} (hk : 0 < k)
    (hχ : χ.OrderDvd k) {μ : G E Ω →* (Qbar l)ˣ} (hμ : Continuous μ) (hL : IsLAdicOf art ι χ 0 μ)
    (hr : IsPstAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype))
    {ξ : (w.adicCompletion E)ˣ →* ℂˣ} (hξ : GlobalTheory.NPin.IsComp χ w ξ) {rc} (H : IsRec h rc) :
    wdAt P ι Bw h hj ((rk1 μ).comp (Dec (F := E) A).subtype) =
      rc (cls (GlobalTheory.SplitRead.Irr.ofDet 1 ξ hξ.1).toIrrRep) := by
  obtain ⟨a, ha', hs, e⟩ := rhs_eq h hξ H
  rw [e]
  have ho : IsOpen (μ.ker : Set (G E Ω)) :=
    isOpen_ker_of_pow μ hμ hk fun g => DFunLike.congr_fun (hL.pow_eq_one ha.quot.surjective hχ) g
  have ho2 : IsOpen {g : GK Bw.Kw | μ (Bw.e.symm g : Dec (F := E) A) = 1} :=
    ho.preimage (continuous_subtype_val.comp Bw.e_symm_cont)
  obtain ⟨U, hU, hU'⟩ := isOpen_induced_iff.1 ho2
  have h1 : (1 : GQ l) ∈ U := by
    have : (1 : GK Bw.Kw) ∈ Subtype.val ⁻¹' U := by rw [hU']; simp
    exact this
  obtain ⟨K', hK1, hK2⟩ := (krullTopology_mem_nhds_one_iff _ _ U).1 (hU.mem_nhds h1)
  have := nontrivial_B P
  refine eq_lpOfChar h _ (Test.lpDim_wdAt P ι Bw h hj _) _ _ fun σ => ?_
  have key := mem_eig_wdAt P ι Bw h hj μ hr 1 one_ne_zero 1 one_ne_zero (by simp) (fun _ => 1) (by simp) (by simp)
    ⟨K', hK1⟩ (fun g hg => by
      have : Bw.e g ∈ Subtype.val ⁻¹' U := hK2 hg
      rw [hU'] at this
      have h2 : μ g = 1 := by simpa using this
      simp [h2]) σ
  rw [hL.loc_away (Or.inr rfl) _ _ (ha'.glob art ha σ)] at key
  simpa using key

theorem conclusion_abs {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) {n : (E →+* ℂ) → ℤ}
    {μ : G E Ω →* (Qbar l)ˣ} (hμ : Continuous μ) (hL : IsLAdicOf art ι (Model.absPow E (1 : ℕ)) n μ)
    (hr : IsPstAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype))
    {ξ : (w.adicCompletion E)ˣ →* ℂˣ} (hξ : GlobalTheory.NPin.IsComp (Model.absPow E (1 : ℕ)) w ξ) {rc} (H : IsRec h rc) :
    wdAt P ι Bw h hj ((rk1 μ).comp (Dec (F := E) A).subtype) =
      rc (cls (GlobalTheory.SplitRead.Irr.ofDet 1 ξ hξ.1).toIrrRep) := by
  obtain ⟨a, ha', hs, e⟩ := rhs_eq h hξ H
  rw [e]
  have hμ' := CharAboveModel.eq_cyc_pow ha hμ hL
  rw [pow_one] at hμ'
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have := nontrivial_B P
  have hcyc : ∀ g : Dec (F := E) A, (μ g : Om l) = algebraMap _ _ (P.χQ (Bw.e g) : ℚ_[l]) := fun g => by
    rw [GlobalTheory.Survey.CrystallineCharacterRatio.chi_eq_cyc P Bw.j (g : G E Ω) (Bw.e g : GQ l) (Bw.e_comm g), hμ', cyc_eq_map_cycZ]
    rfl
  refine eq_lpOfChar h _ (Test.lpDim_wdAt P ι Bw h hj _) _ _ fun σ => ?_
  have key := mem_eig_wdAt P ι Bw h hj μ hr (tInv P) (fun h0 => by simpa [h0] using tInv_mul P) (l : ℚ_[l])⁻¹
    (inv_ne_zero hl) (by rw [eq_inv_smul_iff₀ hl, smul_phiB_tInv]) (fun g => P.χQ g) (fun g => Units.ne_zero _)
    (smul_actQ_tInv P) Bw.Kw (fun g _ => hcyc g) σ
  have h2 : (μ σ : Om l) = algebraMap _ _ (P.χQ (weilToGK Bw h σ) : ℚ_[l]) := hcyc ⟨σ, Weil_le_Dec h σ.2⟩
  rw [h2, ← map_mul, mul_inv_cancel_left₀ (Units.ne_zero _), inv_zpow', neg_neg, map_zpow₀, map_zpow₀, map_natCast,
    map_natCast, alpha, zpow_mul, zpow_natCast, ← Nat.cast_pow, ← normV_eq_pow (hj.mem_placesOver h)] at key
  convert key using 1
  have hu := (Model.absPow_isAbsPow E (1 : ℕ)).1 w
  have hval := (Model.absPow_isAbsPow E (1 : ℕ)).2.1 w
  set χ := Model.absPow E (1 : ℕ)
  have e1 : ∀ x, χ.loc w x = χ.val w ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x := fun x => by
    have h2 := unif_spec w
    have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
    have h1 : IsUnitAt w (x * (atFin w (unif w) ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
        map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, GlobalTheory.SmGL.SphCompletion.ord_completion]
      simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
      rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
    have h3 := hu _ h1
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
    exact h3
  rw [MonoidHom.comp_apply, e1, ha'.ord_eq, Units.val_zpow_eq_zpow_val, hval]
  simp [Complex.cpow_neg, normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

omit P Bw h hj in

theorem hypotheses_met (hA : GlobalArtinReciprocity) (hL : LocalLanglandsGL) (hw : w ∈ placesOver E l) :
    ∃ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) ∧ ∃ art : Ideles E →* Gab E Ω, IsGlobalArtin art ∧
      ∃ μ : G E Ω →* (Qbar l)ˣ, IsAlgPos (Model.absPow E (1 : ℕ)) (fun _ => ((1 : ℕ) : ℤ)) ∧ Continuous μ ∧
      IsLAdicOf art ι (Model.absPow E (1 : ℕ)) (fun _ => ((1 : ℕ) : ℤ)) μ ∧
      ∃ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (LL : FinExt l)
        (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL LL)), GlobalTheory.Pst.Induces Bw ∧
        (∃ ξ, GlobalTheory.NPin.IsComp (Model.absPow E (1 : ℕ)) w ξ) ∧ ∃ rc, IsRec h rc := by
  obtain ⟨P, AI, hT⟩ := GlobalTheory.MemLoc.exists_locPrime_tied l
  obtain ⟨art, ha⟩ := hA E Ω
  obtain ⟨μ, h1, h2, h3, A, h, LL, Bw, hj, -⟩ := CharAboveModel.hypotheses_met ι art ha 1 w hw
  exact ⟨P, AI, hT, art, ha, μ, h1, h2, h3, A, h, LL, Bw, hj, ⟨_, isComp_loc _⟩, (hL.1 E Ω A w h).exists⟩

end GlobalTheory.Published.ParamAboveModel

end
