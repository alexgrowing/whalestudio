import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrComb

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem slice_left {A S A' : HSp D} {K : WO A S → WO S A' → ℂ} (hK : IsBiTheta ψ A S A' K) (v : WO S A') :
    IsThetaFunO ψ A S (fun u => K u v) := by
  refine ⟨fun γ w => hK.quasiL γ w v, ?_, hK.cont.comp (continuous_id.prodMk continuous_const), fun k L hL hLf w => ?_⟩
  · obtain ⟨U, hU, h⟩ := hK.levL
    exact ⟨U, hU, fun a ha ha' => h a ha ha' v⟩
  · have := hK.smooth k L 0 hL continuous_zero hLf (fun _ => by simp) w v
    simpa using this

theorem slice_right {A S A' : HSp D} {K : WO A S → WO S A' → ℂ} (hK : IsBiTheta ψ A S A' K) (u : WO A S) :
    IsThetaFunO ψ S A' (K u) := by
  refine ⟨fun γ w => hK.quasiR γ u w, ?_, hK.cont.comp (continuous_const.prodMk continuous_id), fun k L hL hLf w => ?_⟩
  · obtain ⟨U, hU, h⟩ := hK.levR
    exact ⟨U, hU, fun a ha ha' => h a ha ha' u⟩
  · have := hK.smooth k 0 L continuous_zero hL (fun _ => by simp) hLf u w
    simpa using this

theorem actO_real {S T : HSp D} {g : GA D S} {h : GA D T} (hg : g ∈ GinfC S) (hh : h ∈ GinfC T) {x : WO S T}
    (hx : x.map (infPart D) = 0) : actO S T g h x = x := by
  have e1 : (Formalism.L2.Theta.mt S g⁻¹).map (finPart D) = 1 := congrArg Units.val (show finHom S g⁻¹ = 1 from inv_mem hg)
  have e2 : (Formalism.L2.Theta.mt T h).map (finPart D) = 1 := congrArg Units.val (show finHom T h = 1 from hh)
  have e3 : (actO S T g h x).map (infPart D) = x.map (infPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hx, Matrix.mul_zero, Matrix.zero_mul]
  have e4 : (actO S T g h x).map (finPart D) = x.map (finPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, e1, e2, Matrix.mul_one, Matrix.one_mul]
  exact Matrix.ext fun i j => GlobalTheory.SplitScalar.adele_ext (congrFun (congrFun e3 i) j) (congrFun (congrFun e4 i) j)

theorem nsmul_fin {S T : HSp D} {x : WO S T} (hx : x.map (infPart D) = 0) (n : ℕ) : (n • x).map (infPart D) = 0 := by
  ext i j
  have := congrFun (congrFun hx i) j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply] at this ⊢
  rw [nsmul_eq_mul, RingHom.map_mul, this, mul_zero]

theorem latVac_om {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hom : IsWeilDatumO ψ S T χS χT om)
    {g : GA D S} {h : GA D T} (hg : g ∈ GinfC S) (hh : h ∈ GinfC T) {LS : Set (Fin S.rank → D.host.E)}
    {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hl : IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) f) :
    IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) (om (g, h) f) := by
  refine ⟨fun u hu => ?_, fun e he u hu hu' => ?_⟩
  · calc heisO ψ S T (2 • u) (om (g, h) f) = heisO ψ S T (actO S T g h (2 • u)) (om (g, h) f) := by
          rw [actO_real hg hh (nsmul_fin (GlobalTheory.SplitScalar.latO_fin hu) 2)]
      _ = om (g, h) (heisO ψ S T (2 • u) f) := (hom.om_heis g h _ f hf).symm
      _ = om (g, h) f := by rw [hl.1 u hu]
  · calc heisO ψ S T u (om (g, h) f) = heisO ψ S T (actO S T g h u) (om (g, h) f) := by
          rw [actO_real hg hh (GlobalTheory.SplitScalar.latO_fin hu)]
      _ = om (g, h) (heisO ψ S T u f) := (hom.om_heis g h _ f hf).symm
      _ = om (g, h) f := by rw [hl.2 e he u hu hu']

theorem latVac_opR {A S A' : HSp D} {Λ : AddSubgroup (WO A S)} {K : WO A S → WO S A' → ℂ}
    (hK : ∀ v, IsLatVac (heisO ψ A S) Λ (fun u => K u v)) (T : Module.End ℂ (WO S A' → ℂ)) (v : WO S A') :
    IsLatVac (heisO ψ A S) Λ (fun u => T (K u) v) := by
  have key : ∀ w, (∀ v', heisO ψ A S w (fun u => K u v') = fun u => K u v') →
      heisO ψ A S w (fun u => T (K u) v) = fun u => T (K u) v := by
    intro w hw
    funext u
    have e : K u = ψ (symplOH A S u w) • K (u + w) := funext fun v' => (congrFun (hw v') u).symm
    rw [e, map_smul]
    rfl
  exact ⟨fun u hu => key _ fun v' => (hK v').1 u hu, fun e he u hu hu' => key _ fun v' => (hK v').2 e he u hu hu'⟩

theorem latVac_opL {A S A' : HSp D} {Λ : AddSubgroup (WO S A')} {K : WO A S → WO S A' → ℂ}
    (hK : ∀ u, IsLatVac (heisO ψ S A') Λ (K u)) (T : Module.End ℂ (WO A S → ℂ)) (u : WO A S) :
    IsLatVac (heisO ψ S A') Λ (fun v => T (fun u' => K u' v) u) := by
  have key : ∀ w, (∀ u', heisO ψ S A' w (K u') = K u') →
      heisO ψ S A' w (fun v => T (fun u' => K u' v) u) = fun v => T (fun u' => K u' v) u := by
    intro w hw
    funext v
    have e : (fun u' => K u' v) = ψ (symplOH S A' v w) • fun u' => K u' (v + w) :=
      funext fun u' => (congrFun (hw u') v).symm
    rw [e, map_smul]
    rfl
  exact ⟨fun v hv => key _ fun u' => (hK u').1 v hv, fun e he v hv hv' => key _ fun u' => (hK u').2 e he v hv hv'⟩

def latNbhd (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) : AddSubgroup (WO S T) where
  carrier := {x | ∃ l ∈ latO S T LS LT (fun _ => True), (x - 2 • l).map (finPart D) = 0}
  zero_mem' := ⟨0, (latO S T LS LT fun _ => True).zero_mem, by ext i j; simp⟩
  add_mem' := by
    rintro x y ⟨l, hl, h⟩ ⟨l', hl', h'⟩
    refine ⟨l + l', (latO S T LS LT fun _ => True).add_mem hl hl', ?_⟩
    ext i j
    have e := congrFun (congrFun h i) j
    have e' := congrFun (congrFun h' i) j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply,
      RingHom.map_sub, RingHom.map_add, nsmul_eq_mul, RingHom.map_mul] at e e' ⊢
    linear_combination e + e'
  neg_mem' := by
    rintro x ⟨l, hl, h⟩
    refine ⟨-l, (latO S T LS LT fun _ => True).neg_mem hl, ?_⟩
    ext i j
    have e := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.zero_apply,
      RingHom.map_sub, RingHom.map_neg, nsmul_eq_mul, RingHom.map_mul] at e ⊢
    linear_combination -e

theorem eq_two_smul {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {x : WO S T}
    (hx : x ∈ latNbhd S T LS LT) (hx' : x.map (infPart D) = 0) :
    ∃ l ∈ latO S T LS LT (fun _ => True), x = 2 • l := by
  obtain ⟨l, hl, h⟩ := hx
  refine ⟨l, hl, ?_⟩
  have hl0 := GlobalTheory.SplitScalar.latO_fin hl
  ext i j
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · have e1 := congrFun (congrFun hx' i) j
    have e2 := congrFun (congrFun hl0 i) j
    simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul] at e1 e2 ⊢
    rw [e1, e2, mul_zero]
  · have e := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.zero_apply, RingHom.map_sub] at e
    exact sub_eq_zero.1 e

theorem biTheta_of_vac {A S A' : HSp D} {LA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)}
    {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {LA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)}
    (hLA : IsSelfDualC A LA) (hLS : IsSelfDualC S LS) (hLA' : IsSelfDualC A' LA') {C : WO A S → WO S A' → ℂ}
    (hv : IsBiVac ψ A S A' LA LS LA' C) (hs : IsBiSmooth C) : IsBiTheta ψ A S A' C := by
  refine ⟨hv.cont, hs, fun γ u v => ((hv.left v).1.quasi γ u), fun γ u v => ((hv.right u).1.quasi γ v), ?_, ?_⟩
  · refine ⟨latNbhd A S LA LS, GlobalTheory.LatOpen.isOpen_nsmul_latO D A S LA LS hLA hLS 2 two_pos, fun a ha ha' v => ?_⟩
    obtain ⟨l, hl, rfl⟩ := eq_two_smul ha ha'
    exact (hv.left v).2.1 l hl
  · refine ⟨latNbhd S A' LS LA', GlobalTheory.LatOpen.isOpen_nsmul_latO D S A' LS LA' hLS hLA' 2 two_pos, fun a ha ha' u => ?_⟩
    obtain ⟨l, hl, rfl⟩ := eq_two_smul ha ha'
    exact (hv.right u).2.1 l hl

theorem om_comb {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hom : IsWeilDatumO ψ S T χS χT om)
    {g : GA D S} {h : GA D T} (hg : g ∈ GinfC S) (hh : h ∈ GinfC T) {c : WO S T →₀ ℂ} (hc : IsFinComb c)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : om (g, h) (comb ψ S T c f) = comb ψ S T c (om (g, h) f) := by
  unfold comb
  rw [map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [map_smul, hom.om_heis g h x f hf, actO_real hg hh (hc x hx)]

theorem op_combR {A S A' : HSp D} (T : Module.End ℂ (WO A S → ℂ)) (c : WO S A' →₀ ℂ) (K : WO A S → WO S A' → ℂ)
    (v : WO S A') : T (fun u => comb ψ S A' c (K u) v) = fun u => comb ψ S A' c (fun v' => T (fun u' => K u' v') u) v := by
  have e : (fun u => comb ψ S A' c (K u) v) =
      ∑ y ∈ c.support, (c y * ψ (symplOH S A' v y)) • fun u => K u (v + y) := by
    funext u
    simp only [comb, Finset.sum_apply, Pi.smul_apply, heisO, smul_eq_mul, mul_assoc]
  rw [e, map_sum]
  funext u
  simp only [comb, Finset.sum_apply, Pi.smul_apply, heisO, smul_eq_mul, map_smul, mul_assoc]

theorem op_combL {A S A' : HSp D} (T : Module.End ℂ (WO S A' → ℂ)) (c : WO A S →₀ ℂ) (K : WO A S → WO S A' → ℂ)
    (u : WO A S) : T (fun v => comb ψ A S c (fun u' => K u' v) u) = fun v => comb ψ A S c (fun u' => T (K u') v) u := by
  have e : (fun v => comb ψ A S c (fun u' => K u' v) u) =
      ∑ x ∈ c.support, (c x * ψ (symplOH A S u x)) • K (u + x) := by
    funext v
    simp only [comb, Finset.sum_apply, Pi.smul_apply, heisO, smul_eq_mul, mul_assoc]
  rw [e, map_sum]
  funext v
  simp only [comb, Finset.sum_apply, Pi.smul_apply, heisO, smul_eq_mul, map_smul, mul_assoc]

theorem comb_apply {S T : HSp D} (c : WO S T →₀ ℂ) (g : WO S T → ℂ) (u : WO S T) :
    comb ψ S T c g u = ∑ x ∈ c.support, c x * (ψ (symplOH S T u x) * g (u + x)) := by
  simp only [comb, Finset.sum_apply, Pi.smul_apply, heisO, smul_eq_mul]

theorem isOpen_ker {S T : HSp D} (hψ : IsStdChar D ψ (-1)) {x : WO S T} (hx : x.map (infPart D) = 0) :
    IsOpen {w : WO S T | ψ (symplOH S T w x) = 1} := by
  let K : AddSubgroup (WO S T) :=
    { carrier := {w | ψ (symplOH S T w x) = 1}
      zero_mem' := by
        show ψ _ = 1
        rw [GlobalTheory.FinTranslate.symplOH_zero_left, ψ.map_zero_eq_one]
      add_mem' := fun {a b} ha hb => by
        have ha' : ψ _ = 1 := ha
        have hb' : ψ _ = 1 := hb
        show ψ _ = 1
        rw [GlobalTheory.FinTranslate.symplOH_add_left, AddChar.map_add_eq_mul, ha', hb', one_mul]
      neg_mem' := fun {a} ha => by
        have ha' : ψ _ = 1 := ha
        show ψ _ = 1
        have := AddChar.map_add_eq_mul ψ (symplOH S T a x) (symplOH S T (-a) x)
        rw [← GlobalTheory.FinTranslate.symplOH_add_left, add_neg_cancel, GlobalTheory.FinTranslate.symplOH_zero_left, ψ.map_zero_eq_one,
          ha', one_mul] at this
        exact this.symm }
  show IsOpen (K : Set (WO S T))
  refine K.isOpen_of_mem_nhds (g := 0) ?_
  have h1 : Continuous fun w : WO S T => (symplOH S T w x).2 :=
    continuous_snd.comp (GlobalTheory.FinTranslate.continuous_symplOH S T x)
  have h2 := h1.continuousAt.preimage_mem_nhds (x := 0) (t := {a | ψ (pairA D.host.F 0 a) = 1})
    (by rw [GlobalTheory.FinTranslate.symplOH_zero_left]; exact GlobalTheory.FinTranslate.ker_mem_nhds hψ.1.1 hψ.1.2.1)
  refine Filter.mem_of_superset h2 fun w hw => ?_
  have h3 : GlobalTheory.FinTranslate.eInf D * symplOH S T w x = 0 := by
    rw [← GlobalTheory.FinTranslate.symplOH_smul_right, GlobalTheory.FinTranslate.smul_fin hx, GlobalTheory.FinTranslate.symplOH_zero_right]
  have h4 : symplOH S T w x = pairA D.host.F 0 (symplOH S T w x).2 :=
    Prod.ext ((one_mul _).symm.trans (congrArg Prod.fst h3)) rfl
  show ψ _ = 1
  rw [h4]; exact hw

theorem exists_orth {S T : HSp D} (hψ : IsStdChar D ψ (-1)) {c : WO S T →₀ ℂ} (hc : IsFinComb c) :
    ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ w ∈ U, ∀ x ∈ c.support, ψ (symplOH S T w x) = 1 := by
  let U : AddSubgroup (WO S T) :=
    { carrier := {w | ∀ x ∈ c.support, ψ (symplOH S T w x) = 1}
      zero_mem' := fun x _ => by rw [GlobalTheory.FinTranslate.symplOH_zero_left, ψ.map_zero_eq_one]
      add_mem' := fun {a b} ha hb x hx => by
        rw [GlobalTheory.FinTranslate.symplOH_add_left, AddChar.map_add_eq_mul, ha x hx, hb x hx, one_mul]
      neg_mem' := fun {a} ha x hx => by
        have := AddChar.map_add_eq_mul ψ (symplOH S T a x) (symplOH S T (-a) x)
        rw [← GlobalTheory.FinTranslate.symplOH_add_left, add_neg_cancel, GlobalTheory.FinTranslate.symplOH_zero_left, ψ.map_zero_eq_one,
          ha x hx, one_mul] at this
        exact this.symm }
  refine ⟨U, ?_, fun w hw => hw⟩
  have e : (U : Set (WO S T)) = ⋂ x ∈ c.support, {w | ψ (symplOH S T w x) = 1} := by
    ext w
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [e]
  exact isOpen_biInter_finset fun x hx => isOpen_ker hψ (hc x hx)

theorem heisO_comb {S T : HSp D} {c : WO S T →₀ ℂ} {w : WO S T} (hw : ∀ x ∈ c.support, ψ (symplOH S T w x) = 1)
    {g : WO S T → ℂ} (hg : heisO ψ S T w g = g) : heisO ψ S T w (comb ψ S T c g) = comb ψ S T c g := by
  unfold comb
  rw [GlobalTheory.SplitScalar.heisO_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have h2 : ψ (symplOH S T x w) = 1 := by
    rw [GlobalTheory.FinTranslate.symplOH_skew, AddChar.map_neg_eq_inv, hw x hx, inv_one]
  rw [GlobalTheory.SplitScalar.heisO_smul]
  congr 1
  conv_rhs => rw [← hg]
  rw [GlobalTheory.FinTranslate.heisO_heisO, GlobalTheory.FinTranslate.heisO_heisO, hw x hx, h2, add_comm]

theorem biTheta_combL {A S A' : HSp D} (hψ : IsStdChar D ψ (-1)) {K : WO A S → WO S A' → ℂ}
    (hK : IsBiTheta ψ A S A' K) {c : WO A S →₀ ℂ} (hc : IsFinComb c) :
    IsBiTheta ψ A S A' (fun u v => comb ψ A S c (fun u' => K u' v) u) := by
  have e : (fun u v => comb ψ A S c (fun u' => K u' v) u) =
      fun u v => ∑ x ∈ c.support, c x * (ψ (symplOH A S u x) * K (u + x) v) := by
    funext u v; exact comb_apply c _ u
  refine ⟨?_, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · simp only [comb_apply]
    exact continuous_finset_sum _ fun x _ => continuous_const.mul
      ((hψ.1.1.comp ((GlobalTheory.FinTranslate.continuous_symplOH A S x).comp continuous_fst)).mul
        (hK.cont.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)))
  · intro n L L' hL hL' hLf hL'f u v
    rw [e]
    have e2 : (fun t => ∑ x ∈ c.support, c x * (ψ (symplOH A S (u + L t) x) * K (u + L t + x) (v + L' t))) =
        fun t => ∑ x ∈ c.support, c x * (ψ (symplOH A S u x) * K (u + x + L t) (v + L' t)) := by
      funext t
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_real_fin (hc x hx) (hLf t), add_zero,
        add_right_comm]
    simp only []
    rw [e2]
    exact ContDiff.sum fun x _ => contDiff_const.mul (contDiff_const.mul (hK.smooth n L L' hL hL' hLf hL'f (u + x) v))
  · simp only [comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [add_assoc, hK.quasiL, GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_right]
    have key : ψ (symplOH A S (ratW S A γ) x + symplOH A S u x) * ψ (-(symplOH A S (ratW S A γ) u + symplOH A S (ratW S A γ) x)) =
        ψ (-(symplOH A S (ratW S A γ) u)) * ψ (symplOH A S u x) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]; congr 1; ring
    linear_combination (c x * K (u + x) v) * key
  · simp only [comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hK.quasiR]
    ring
  · obtain ⟨U, hU, hUf⟩ := hK.levL
    obtain ⟨V, hV, hVf⟩ := exists_orth hψ hc
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' v => ?_⟩
    exact heisO_comb (hVf a ha.2) (hUf a ha.1 ha' v)
  · obtain ⟨U, hU, hUf⟩ := hK.levR
    refine ⟨U, hU, fun a ha ha' u => ?_⟩
    funext v
    simp only [heisO, comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have e3 := congrFun (hUf a ha ha' (u + x)) v
    simp only [heisO] at e3
    rw [← e3]
    ring

theorem biTheta_combR {A S A' : HSp D} (hψ : IsStdChar D ψ (-1)) {K : WO A S → WO S A' → ℂ}
    (hK : IsBiTheta ψ A S A' K) {c : WO S A' →₀ ℂ} (hc : IsFinComb c) :
    IsBiTheta ψ A S A' (fun u v => comb ψ S A' c (K u) v) := by
  have e : (fun u v => comb ψ S A' c (K u) v) =
      fun u v => ∑ y ∈ c.support, c y * (ψ (symplOH S A' v y) * K u (v + y)) := by
    funext u v; exact comb_apply c _ v
  refine ⟨?_, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · simp only [comb_apply]
    exact continuous_finset_sum _ fun y _ => continuous_const.mul
      ((hψ.1.1.comp ((GlobalTheory.FinTranslate.continuous_symplOH S A' y).comp continuous_snd)).mul
        (hK.cont.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))))
  · intro n L L' hL hL' hLf hL'f u v
    rw [e]
    have e2 : (fun t => ∑ y ∈ c.support, c y * (ψ (symplOH S A' (v + L' t) y) * K (u + L t) (v + L' t + y))) =
        fun t => ∑ y ∈ c.support, c y * (ψ (symplOH S A' v y) * K (u + L t) (v + y + L' t)) := by
      funext t
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_real_fin (hc y hy) (hL'f t), add_zero,
        add_right_comm]
    simp only []
    rw [e2]
    exact ContDiff.sum fun y _ => contDiff_const.mul (contDiff_const.mul (hK.smooth n L L' hL hL' hLf hL'f u (v + y)))
  · simp only [comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hK.quasiL]
    ring
  · simp only [comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [add_assoc, hK.quasiR, GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_right]
    have key : ψ (symplOH S A' (ratW A' S γ) y + symplOH S A' v y) * ψ (-(symplOH S A' (ratW A' S γ) v + symplOH S A' (ratW A' S γ) y)) =
        ψ (-(symplOH S A' (ratW A' S γ) v)) * ψ (symplOH S A' v y) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]; congr 1; ring
    linear_combination (c y * K u (v + y)) * key
  · obtain ⟨U, hU, hUf⟩ := hK.levL
    refine ⟨U, hU, fun a ha ha' v => ?_⟩
    funext u
    simp only [heisO, comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have e3 := congrFun (hUf a ha ha' (v + y)) u
    simp only [heisO] at e3
    rw [← e3]
    ring
  · obtain ⟨U, hU, hUf⟩ := hK.levR
    obtain ⟨V, hV, hVf⟩ := exists_orth hψ hc
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' u => ?_⟩
    exact heisO_comb (hVf a ha.2) (hUf a ha.1 ha' u)

end GlobalTheory.FrComb

end
