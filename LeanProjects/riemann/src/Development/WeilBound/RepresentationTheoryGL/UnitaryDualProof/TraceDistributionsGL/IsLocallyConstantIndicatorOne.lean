import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.PhiIndep

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.BZMir GroundTheory.Automorphic.Whittaker
  GlobalTheory.SplitDict

namespace PositivityTheory.RgUd.AB.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_supportedIn_iff {X : Type*} [TopologicalSpace X] {U : Set X} {f : X → ℂ} :
    f ∈ supportedIn U ↔ f ∈ SB X ∧ Function.support f ⊆ U := by
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

theorem mem_supportedIn_univ_iff {X : Type*} [TopologicalSpace X] {f : X → ℂ} :
    f ∈ supportedIn (Set.univ : Set X) ↔ f ∈ SB X := by
  rw [mem_supportedIn_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, Set.subset_univ _⟩⟩

def recCjHomeo {n : ℕ} (g : GL (Fin (n + 1)) k) : Mx k n ≃ₜ Mx k n where
  toFun := cj g
  invFun := cj g⁻¹
  left_inv x := by
    simp only [cj, inv_inv]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul,
      Matrix.mul_one]
  right_inv x := by
    simp only [cj, inv_inv]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  continuous_toFun := by
    unfold cj
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := by
    unfold cj
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

def mvHomeo {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hAB : A * B = 1) (hBA : B * A = 1) :
    Vc k n ≃ₜ Vc k n where
  toFun w := A *ᵥ w
  invFun w := B *ᵥ w
  left_inv w := by simp only [mulVec_mulVec, hBA, one_mulVec]
  right_inv w := by simp only [mulVec_mulVec, hAB, one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem comp_mem_SB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {f : Y → ℂ}
    (hf : f ∈ SB Y) : f ∘ e ∈ SB X :=
  (bijOn_comp e).mapsTo hf

theorem cj_comp_mem {n : ℕ} (g : GL (Fin (n + 1)) k) {f : Mx k n → ℂ} (hf : f ∈ SB (Mx k n)) : f ∘ cj g ∈ SB (Mx k n) :=
  comp_mem_SB (recCjHomeo g) hf

theorem act_mem {n : ℕ} (g : GL (Fin (n + 1)) k) {F : Mx k n × Vc k n → ℂ} (hF : F ∈ SB (Mx k n × Vc k n)) :
    (fun p : Mx k n × Vc k n => F ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) * p.1 *
      ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k),
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ p.2)) ∈ SB (Mx k n × Vc k n) :=
  comp_mem_SB ((recCjHomeo g).prodCongr (mvHomeo (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Units.mul_inv g) (Units.inv_mul g))) hF

theorem tw_mem {n : ℕ} (h : GL (Fin (n + 1)) k) {F : Mx k n × Vc k n → ℂ} (hF : F ∈ SB (Mx k n × Vc k n)) :
    (fun q : Mx k n × Vc k n => F (cj h⁻¹ q.1, (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ q.2)) ∈
      SB (Mx k n × Vc k n) :=
  comp_mem_SB ((recCjHomeo h⁻¹).prodCongr (mvHomeo (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ
    ((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ
    (by rw [← transpose_mul, Units.inv_mul, transpose_one]) (by rw [← transpose_mul, Units.mul_inv, transpose_one]))) hF

theorem isLocallyConstant_indicator_one {Y : Type*} [TopologicalSpace Y] {E : Set Y} (hE : IsClopen E) :
    IsLocallyConstant (E.indicator (1 : Y → ℂ)) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun y => ?_
  by_cases hy : y ∈ E
  · filter_upwards [hE.isOpen.mem_nhds hy] with z hz
    rw [Set.indicator_of_mem hz, Set.indicator_of_mem hy]
    rfl
  · filter_upwards [hE.isClosed.isOpen_compl.mem_nhds hy] with z hz
    rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hy]

theorem tens_mem {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y] {f : X → ℂ}
    (hf : f ∈ SB X) {E : Set Y} (hEo : IsOpen E) (hEc : IsCompact E) :
    (fun q : X × Y => f q.1 * E.indicator 1 q.2) ∈ SB (X × Y) := by
  refine ⟨(hf.1.comp_continuous continuous_fst).mul
    ((isLocallyConstant_indicator_one ⟨hEc.isClosed, hEo⟩).comp_continuous continuous_snd),
    HasCompactSupport.intro (hf.2.isCompact.prod hEc) fun q hq => ?_⟩
  by_cases h1 : q.1 ∈ tsupport f
  · have h2 : q.2 ∉ E := fun h2 => hq ⟨h1, h2⟩
    simp [Set.indicator_of_notMem h2]
  · simp [image_eq_zero_of_notMem_tsupport h1]

theorem slice_fst_mem {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] {g : X × Y → ℂ}
    (hg : g ∈ SB (X × Y)) (y : Y) : (fun x => g (x, y)) ∈ SB X :=
  ⟨hg.1.comp_continuous (by fun_prop), HasCompactSupport.intro (hg.2.isCompact.image continuous_fst) fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx ⟨_, h, rfl⟩⟩

theorem zero_mem_box {m : Type*} (s : kˣ) : (0 : m → k) ∈ box m s := by
  intro i _
  simp [cball]

section Meas

variable [MeasurableSpace k] [BorelSpace k]

theorem integrable_slice (ν : Measure k) [ν.IsAddHaarMeasure] {T : Type} [TopologicalSpace T] {n : Type} [Fintype n]
    {ψ : AddChar k Circle} {c : kˣ} (hψ : HasConductor ψ c) {F : T × (n → k) → ℂ} (hF : F ∈ SB (T × (n → k)))
    (z : T × (n → k)) : Integrable (fun x => F (z.1, x) * (ψ (x ⬝ᵥ z.2) : ℂ)) (Measure.pi fun _ => ν) := by
  haveI := secondCountable k
  haveI := t2Space k
  have hs := slice_mem_SB hF z.1
  have h2 : IsLocallyConstant fun x : n → k => ((ψ (x ⬝ᵥ z.2) : Circle) : ℂ) :=
    (hψ.isLocallyConstant.comp_continuous (continuous_id.dotProduct continuous_const)).comp _
  exact (hs.1.mul h2).continuous.integrable_of_hasCompactSupport hs.2.mul_right

theorem pf_lin (ν : Measure k) [ν.IsAddHaarMeasure] {T : Type} [TopologicalSpace T] {n : Type} [Fintype n]
    {ψ : AddChar k Circle} {c : kˣ} (hψ : HasConductor ψ c) {F G : T × (n → k) → ℂ} (hF : F ∈ SB (T × (n → k)))
    (hG : G ∈ SB (T × (n → k))) (a b : ℂ) :
    pf ψ (Measure.pi fun _ => ν) (a • F + b • G) = a • pf ψ (Measure.pi fun _ => ν) F + b • pf ψ (Measure.pi fun _ => ν) G := by
  funext z
  simp only [pf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((integrable_slice ν hψ hF z).const_mul a)
    ((integrable_slice ν hψ hG z).const_mul b)]
  congr 1
  funext x
  ring

end Meas

theorem recover (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PhiIndep k → PhiLin k → PhiInt k → PhiNear k → PfAct k → LtEquiv k → Recover k := by
  intro _ hLin hInt hNear hPf hLt hT n Λ hP
  borelize k
  have := secondCountable k
  have := t2Space k
  obtain ⟨-, ⟨ψ, -, -, hψ⟩, ν, hν⟩ := conductor_exists k
  have := hν.1
  set μ : Measure (Vc k n) := Measure.pi fun _ => ν with hμ
  have hb := pf_bijOn (T := Mx k n) (n := Fin (n + 1)) ν hψ
  set Fi := Function.invFunOn (pf ψ μ) {f | f ∈ SB (Mx k n × Vc k n)} with hFi
  have Fi_mem : ∀ f ∈ SB (Mx k n × Vc k n), Fi f ∈ SB (Mx k n × Vc k n) := fun f hf => hb.surjOn.mapsTo_invFunOn hf
  have pf_Fi : ∀ f ∈ SB (Mx k n × Vc k n), pf ψ μ (Fi f) = f := fun f hf => hb.surjOn.rightInvOn_invFunOn hf
  have Fi_pf : ∀ F ∈ SB (Mx k n × Vc k n), Fi (pf ψ μ F) = F := fun F hF => hb.injOn.leftInvOn_invFunOn hF
  have pfL := fun {F G : Mx k n × Vc k n → ℂ} (hF : F ∈ SB _) (hG : G ∈ SB _) (a b : ℂ) => pf_lin ν hψ hF hG a b
  have pfS : ∀ F ∈ SB (Mx k n × Vc k n), ∀ a : ℂ, pf ψ μ (a • F) = a • pf ψ μ F := fun F hF a => by
    have := pfL hF hF a 0
    simpa using this
  have FiL : ∀ f ∈ SB (Mx k n × Vc k n), ∀ g ∈ SB (Mx k n × Vc k n), ∀ a b : ℂ,
      Fi (a • f + b • g) = a • Fi f + b • Fi g := by
    intro f hf g hg a b
    have h1 : a • Fi f + b • Fi g ∈ SB (Mx k n × Vc k n) :=
      add_mem (Submodule.smul_mem _ _ (Fi_mem f hf)) (Submodule.smul_mem _ _ (Fi_mem g hg))
    have := Fi_pf _ h1
    rw [pfL (Fi_mem f hf) (Fi_mem g hg), pf_Fi f hf, pf_Fi g hg] at this
    exact this
  have ltL : ∀ F ∈ SB (Mx k n × Vc k n), ∀ G ∈ SB (Mx k n × Vc k n), ∀ a b : ℂ,
      lt ν Λ (a • F + b • G) = a * lt ν Λ F + b * lt ν Λ G := by
    intro F hF G hG a b
    unfold lt
    rw [hLin n Λ F hF G hG a b]
    simp only [Pi.add_apply]
    rw [integral_add ((hInt ν n Λ hP F hF).smul a) ((hInt ν n Λ hP G hG).smul b)]
    simp only [Pi.smul_apply]
    rw [integral_smul, integral_smul, smul_eq_mul, smul_eq_mul]
  have ltS : ∀ F ∈ SB (Mx k n × Vc k n), ∀ a : ℂ, lt ν Λ (a • F) = a * lt ν Λ F := fun F hF a => by
    have := ltL F hF F hF a 0
    simpa using this
  let Ξ₀ : SB (Mx k n × Vc k n) →ₗ[ℂ] ℂ :=
    { toFun := fun f => lt ν Λ (Fi f)
      map_add' := fun f g => by
        have e := FiL f f.2 g g.2 1 1
        simp only [one_smul] at e
        have e2 := ltL _ (Fi_mem f f.2) _ (Fi_mem g g.2) 1 1
        simp only [one_smul, one_mul] at e2
        simp only [Submodule.coe_add, e, e2]
      map_smul' := fun c f => by
        have e := FiL f f.2 f f.2 c 0
        simp only [zero_smul, add_zero] at e
        simp only [SetLike.val_smul, RingHom.id_apply, smul_eq_mul, e, ltS _ (Fi_mem f f.2)] }
  obtain ⟨ξ, hξ⟩ := LinearMap.exists_extend Ξ₀
  have hξf : ∀ f ∈ SB (Mx k n × Vc k n), ξ f = lt ν Λ (Fi f) := fun f hf => LinearMap.congr_fun hξ ⟨f, hf⟩
  have hinv : ∀ (g : GL (Fin (n + 1)) k), ∀ f ∈ SB (Mx k n × Vc k n),
      ξ (fun p : Mx k n × Vc k n => f ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) * p.1 *
        ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k),
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ p.2)) = ξ f := by
    intro g f hf
    have hF := Fi_mem f hf
    have hF' := tw_mem g⁻¹ hF
    have e1 := hPf ν ψ 1 hψ n (Fi f) hF g⁻¹
    set c : ℂ := (((nabs k (Matrix.GeneralLinearGroup.det g⁻¹))⁻¹ : ℝ) : ℂ) with hc
    have hc0 : c ≠ 0 := by
      rw [hc]
      exact Complex.ofReal_ne_zero.2 (inv_ne_zero (nabs_pos k _).ne')
    have e2 : (fun p : Mx k n × Vc k n => f ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) * p.1 *
        ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k),
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ p.2)) =
        pf ψ μ (c⁻¹ • fun q : Mx k n × Vc k n => Fi f (cj g⁻¹⁻¹ q.1,
          ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ q.2)) := by
      rw [pfS _ hF', e1, pf_Fi f hf]
      funext p
      simp only [Pi.smul_apply, smul_eq_mul, cj, inv_inv]
      rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    rw [e2, hξf _ (pf_mem_SB μ hψ (Submodule.smul_mem _ _ hF')), Fi_pf _ (Submodule.smul_mem _ _ hF'),
      ltS _ hF', hLt ν n Λ hP (Fi f) hF g⁻¹, hξf f hf, ← hc, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hzero : ∀ f ∈ SB (Mx k n × Vc k n), (∀ x : Mx k n, f (x, 0) = 0) → ξ f = 0 := by
    intro f hf h0
    have hsupp : Function.support f ⊆ {p : Mx k n × Vc k n | p.2 ≠ 0} := by
      intro p hp h2
      apply hp
      obtain ⟨x, w⟩ := p
      simp only at h2
      subst h2
      exact h0 x
    refine hT (n + 1) ⊥ ?_ ?_ ξ ?_ ?_ f (mem_supportedIn_iff.2 ⟨hf, hsupp⟩)
    · intro a ha b _
      obtain ⟨r, rfl⟩ := Algebra.mem_bot.1 ha
      exact Algebra.commutes r b
    · refine ⟨fun x hx => ?_⟩
      obtain ⟨m, hm⟩ := hx
      obtain ⟨r, hr⟩ := Algebra.mem_bot.1 x.2
      have h1 : ((x : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) ^ m = 0 := by
        simpa using congrArg Subtype.val hm
      have h2 : (algebraMap k (Matrix (Fin (n + 1)) (Fin (n + 1)) k)) (r ^ m) = 0 := by
        rw [map_pow, hr, h1]
      have h3 : r ^ m = 0 := (algebraMap k (Matrix (Fin (n + 1)) (Fin (n + 1)) k)).injective (h2.trans (map_zero _).symm)
      have h4 : r = 0 := by
        by_contra hr0
        exact pow_ne_zero m hr0 h3
      exact Subtype.ext (by rw [← hr, h4, map_zero]; rfl)
    · intro f' _ hz
      have : f' = 0 := funext fun p => hz p fun a ha => by
        obtain ⟨r, rfl⟩ := Algebra.mem_bot.1 ha
        exact Algebra.commutes r p.1
      rw [this, map_zero]
    · intro g _ f' hf'
      exact hinv g f' (mem_supportedIn_univ_iff.1 hf')
  set B : Set (Vc k n) := box (Fin (n + 1)) (1 : kˣ) with hB
  have hBo : IsOpen B := isOpen_box _
  have hBc : IsCompact B := isCompact_box _
  have hB0 : (0 : Vc k n) ∈ B := zero_mem_box _
  let T : (Mx k n → ℂ) →ₗ[ℂ] (Mx k n × Vc k n → ℂ) :=
    { toFun := fun f q => f q.1 * B.indicator 1 q.2
      map_add' := fun f g => by
        funext q
        simp only [Pi.add_apply]
        ring
      map_smul' := fun c f => by
        funext q
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  have hT_apply : ∀ f q, T f q = f q.1 * B.indicator 1 q.2 := fun _ _ => rfl
  refine ⟨ξ ∘ₗ T, ?_, ?_⟩
  · intro g f hf
    have h1 : T (f ∘ cj g) ∈ SB (Mx k n × Vc k n) := tens_mem (cj_comp_mem g hf) hBo hBc
    have h2 : T f ∈ SB (Mx k n × Vc k n) := tens_mem hf hBo hBc
    have h3 := act_mem g h2
    have hd := hzero _ (sub_mem h1 h3) fun x => by
      simp only [Pi.sub_apply, hT_apply, Function.comp_apply, mulVec_zero, Set.indicator_of_mem hB0, cj]
      ring
    rw [map_sub, sub_eq_zero] at hd
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hd, hinv g _ h2]
  · intro f₀ hf₀
    obtain ⟨t, ht⟩ := hNear n Λ hP f₀ hf₀
    have hφ := ht t subset_rfl
    set E : Set (Vc k n) := {w : Vc k n | w - eN k n ∈ box (Fin (n + 1)) t} with hE
    set F : Mx k n × Vc k n → ℂ := fun q => f₀ q.1 * E.indicator 1 q.2 with hFdef
    have hEo : IsOpen E := (isOpen_box t).preimage (continuous_id.sub continuous_const)
    have hEc : IsCompact E := by
      have : E = (fun w => w + eN k n) '' box (Fin (n + 1)) t := by
        ext w
        simp only [hE, Set.mem_ofPred_eq, Set.mem_image]
        exact ⟨fun h => ⟨w - eN k n, h, by abel⟩, fun ⟨u, hu, e⟩ => by rw [← e]; simpa using hu⟩
      rw [this]
      exact (isCompact_box t).image (continuous_id.add continuous_const)
    have hE0 : eN k n ∈ E := by
      simp only [hE, Set.mem_ofPred_eq, sub_self]
      exact zero_mem_box _
    have hF : F ∈ SB (Mx k n × Vc k n) := tens_mem hf₀ hEo hEc
    have hlt : lt ν Λ F = μ.real E * Λ f₀ := by
      unfold lt
      rw [hφ, integral_indicator_const _ hEo.measurableSet, Complex.real_smul]
    have hg := pf_mem_SB μ hψ hF
    have hg0 : ∀ x, pf ψ μ F (x, 0) = μ.real E * f₀ x := by
      intro x
      simp only [pf, hFdef, dotProduct_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
      rw [integral_const_mul, show (E.indicator (1 : Vc k n → ℂ)) = E.indicator (fun _ => (1 : ℂ)) from rfl,
        integral_indicator_const _ hEo.measurableSet, Complex.real_smul, mul_one, mul_comm]
    have h1 : ξ (pf ψ μ F) = lt ν Λ F := by rw [hξf _ hg, Fi_pf F hF]
    have h2 : (fun q : Mx k n × Vc k n => pf ψ μ F (q.1, 0) * B.indicator 1 q.2) = (μ.real E : ℂ) • T f₀ := by
      funext q
      simp only [hg0, Pi.smul_apply, smul_eq_mul, hT_apply]
      ring
    have h3 := hzero _ (sub_mem hg (tens_mem (slice_fst_mem hg 0) hBo hBc)) fun x => by
      simp only [Pi.sub_apply, Set.indicator_of_mem hB0, Pi.one_apply, mul_one, sub_self]
    rw [map_sub, sub_eq_zero, h2, map_smul, h1, hlt, smul_eq_mul] at h3
    have hpos : μ.real E ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]
      exact ⟨(hEo.measure_pos μ ⟨_, hE0⟩).ne', hEc.measure_lt_top.ne⟩
    have hpos' : (μ.real E : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos
    simp only [LinearMap.coe_comp, Function.comp_apply]
    exact mul_left_cancel₀ hpos' h3

theorem coreX (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    Recover k → CoreX k := by
  intro hR hT n Λ hP g f hf
  obtain ⟨L, hL, hΛ⟩ := hR hT n Λ hP
  rw [hΛ _ (cj_comp_mem g hf), hΛ f hf, hL g f hf]

end PositivityTheory.RgUd.AB.Pf
