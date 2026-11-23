import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.CoefficientSpans
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.FinStmt
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.IdealStmt
import Development.WeilBound.ThetaLifts.LeviDeterminants.ActsEx

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Fin

open scoped TensorProduct NNReal Matrix nonZeroDivisors GlobalTheory.VacAny Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LatVac
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d n₁ d₁ : ℕ}
  {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

attribute [local instance] PositivityTheory.ThK.kc_ring PositivityTheory.ThK.adele_t2Space PositivityTheory.ThK.kc_smul

theorem idem_sq (v : Pl F) : idem F v * idem F v = idem F v := by
  have := PositivityTheory.ThK.Vac.liftV_mul v 1 (idem F v)
  rwa [evFin_idem, mul_one] at this

theorem norm_wt (ν : Chr F E) (z : ℕ) (l : (AE F E)ˣ) : ‖wt ν z l‖ = (absE F E l : ℝ) ^ z := by
  rw [wt, norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg NNReal.zero_le_coe]

theorem cont_wt {ν : Chr F E} (hν : Continuous ν) (z : ℕ) : Continuous (wt ν z) :=
  (continuous_subtype_val.comp hν).mul
    ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE)).pow z)

variable (σ X) in

def uSub (v : Pl F) : Subgroup (UA σ X.J) where
  carrier := UAt σ X (evFin F v)
  one_mem' := fun u _ => by rw [show mat (1 : UA σ X.J) = 1 from rfl, sub_self, smul_zero]
  mul_mem' := fun {a b} ha hb u hu => by
    have e : mat (a * b) - 1 = (mat a - 1) * mat b + (mat b - 1) := by
      rw [show mat (a * b) = mat a * mat b from rfl, Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e, smul_add, ← Matrix.smul_mul, ha u hu, hb u hu, Matrix.zero_mul, add_zero]
  inv_mem' := fun {a} ha u hu => by
    have h1 : mat a⁻¹ * mat a = 1 := a.1.inv_mul
    have e : mat a⁻¹ - 1 = -(mat a⁻¹ * (mat a - 1)) := by rw [Matrix.mul_sub, h1, Matrix.mul_one]; abel
    rw [e, smul_neg, ← Matrix.mul_smul, ha u hu, Matrix.mul_zero, neg_zero]

theorem kAt_eq (K : Subgroup (UA σ X.J)) (v : Pl F) : kAt K (evFin F v) = K ⊓ uSub σ X v :=
  congrArg (K ⊓ ·) (Subgroup.closure_eq (uSub σ X v))

theorem kAt_mem {K : Subgroup (UA σ X.J)} {v : Pl F} (k : kAt K (evFin F v)) : k.1 ∈ UAt σ X (evFin F v) :=
  ((kAt_eq K v).le k.2).2

theorem kAt_compact {K : Subgroup (UA σ X.J)} (hK : IsCompact (K : Set (UA σ X.J))) (v : Pl F) : CompactSpace (kAt K (evFin F v)) := by
  refine isCompact_iff_compactSpace.1 ?_
  rw [kAt_eq, Subgroup.coe_inf]
  refine hK.inter_right ?_
  have : (uSub σ X v : Set (UA σ X.J)) = ⋂ u : AF F, ⋂ _ : evFin F v u = 0, {g | u • (mat g - 1) = 0} := by
    ext g; simp only [Set.mem_iInter]; rfl
  rw [this]
  exact isClosed_iInter fun u => isClosed_iInter fun _ =>
    isClosed_eq (((PositivityTheory.ThK.kc_cont_mat X.J).sub continuous_const).const_smul u) continuous_const

theorem tate (hI : IdeleFub) (hJ : IdealId0) (hS : StabEx) {B : Base F E} {M : Model σ X W} {M₁ : Model σ X₁ W₁}
    {H : Plane E n n₁} {H' : Plane E d d₁} {e u ei ev} (hc : Cfg B M M₁ H H' e u) (h : IsEvLoc M M₁ e ei ev) (v : Pl F)
    {K : Subgroup (UA σ X.J)} (m : LocMeas K) (hm : m.Is) {ν : Chr F E} (hν : Continuous ν) {z : ℕ} (hz : 2 ≤ z)
    {φ : Fl F v n d} (hφ : φ ∈ SB _) :
    (∀ y, @Integrable _ _ _ _ (borel _) (fun l : idAt E (evFin F v) => ev v (rv B M v (idem F v • u l.1) φ) y * wt ν z l.1) (m.xf v)) ∧
      (fun y => @integral _ _ _ _ (borel _) (m.xf v) fun l => ev v (rv B M v (idem F v • u l.1) φ) y * wt ν z l.1) ∈ SB _ := by
  letI : MeasurableSpace (idAt E (evFin F v)) := borel _
  haveI : BorelSpace (idAt E (evFin F v)) := ⟨rfl⟩
  haveI := (hm.xf v).1
  obtain ⟨V₀, V₁, c, hu, -, -, hinv, hcomp⟩ := dirs hc
  obtain ⟨r, s, hX⟩ := hc.herm
  obtain ⟨r', s', hW⟩ := hc.skew
  obtain ⟨i, j, hH⟩ := hc.hH
  obtain ⟨i', j', hH'⟩ := hc.hH'
  obtain ⟨𝔞, h𝔞, hin⟩ := hJ F E σ B n d n₁ d₁ X W X₁ W₁ H H' r s r' s' i j i' j' hc.base hX hW hH hH' u
    (hc.ev.imp And.right And.right)
  obtain ⟨-, -, μ, -, -, -, hμ⟩ := hS F E σ B n X r s hc.base hX
  obtain ⟨πi, π, κ, -, hπ, hF⟩ := hI F E σ B n X K m μ hc.base hm hμ 𝔞 z h𝔞 hz
  have hint := ((hF 1 ∅ ∅ continuous_const (Finset.Subset.refl _) (fun w _ x _ => map_one Circle.toUnits)
    (fun w hw => absurd hw (Finset.notMem_empty _))).1 v (Finset.notMem_empty v)).2
  obtain ⟨N, hN, hfix⟩ := exists_level hc.base hX hW M v hφ
  obtain ⟨C, hC, hCΓ⟩ := lat_compact hX hW M v
  let g : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → Fl F v n₁ d₁ := fun w => ev v (schr (psiAt B.ψ v) w φ)
  have hg : IsLocallyConstant g := (schr_lc (psi_lc hc.base v) fun w => rv_sb hc.base M v w hφ).comp (ev v)
  have e1 : ∀ l : (AE F E)ˣ, locCo M.co v (idem F v • u l) = locCo M.co v (c l.1 • V₀) := fun l => by
    rw [locCo_smul, evFin_idem, one_smul, hu]
  have hG : IsLocallyConstant fun l : idAt E (evFin F v) => ev v (rv B M v (idem F v • u l.1) φ) := by
    simp only [rv, e1]
    exact hg.comp_continuous ((cont_loc M v c V₀).comp (Units.continuous_val.comp continuous_subtype_val))
  have hk : ∀ l : (AE F E)ˣ, ev v (rv B M v (idem F v • u l) φ) ≠ 0 → (N : AF F) • idem F v • u l ∈ latAtV X W v := fun l hl => by
    have e2 : idem F v • u l = (idem F v • c l.1) • V₀ := by rw [hu, smul_assoc]
    rw [e2] at hl ⊢
    exact key hc h hinv (hcomp v) hφ N (fun t ht => hfix _ ht) _ (e2 ▸ at_idem v _) hl
  have hN' : (N : Fv F v) ≠ 0 := by
    haveI : CharZero (Fv F v) := algebraRat.charZero _
    exact Nat.cast_ne_zero.2 hN
  refine int_fin (m.xf v) (fun l => ev v (rv B M v (idem F v • u l.1) φ)) (fun l => wt ν z l.1) ?_
    (fun a => (hG.isOpen_fiber a).measurableSet) {l | ev v (rv B M v (idem F v • u l.1) φ) ≠ 0} (fun a ha => not_not.1 ha) ?_ _
    fun l => (h.vac v).2 ▸ Submodule.mem_map_of_mem (rv_sb hc.base M v _ hφ)
  · haveI := isCompact_iff_compactSpace.1 hC
    have hf := (hg.comp_continuous ((continuous_subtype_val (p := (· ∈ C))).const_smul (N : Fv F v)⁻¹)).range_finite
    refine (hf.insert 0).subset ?_
    rintro _ ⟨l, rfl⟩
    by_cases h0 : ev v (rv B M v (idem F v • u l.1) φ) = 0
    · exact Or.inl h0
    · refine Or.inr ⟨⟨_, hCΓ _ (hk _ h0)⟩, ?_⟩
      change g ((N : Fv F v)⁻¹ • locCo M.co v ((N : AF F) • idem F v • u l.1)) = _
      rw [locCo_smul M v (N : AF F), map_natCast, inv_smul_smul₀ hN']
  · have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN
    let lN : (AE F E)ˣ := Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 (N : E) hNE)
    let l₀ := π v lN
    have hl₀ : (l₀.1 : AE F E) = idem F v • (N : AE F E) + (1 - idem F v) • (1 : AE F E) := by
      have := (hπ lN).2 v
      rw [IsPart, show (lN : AE F E) = (N : AE F E) from map_natCast (inclR (F := F) (AF F)) N] at this
      exact this
    have e3 : ∀ l : idAt E (evFin F v), idem F v • u (l₀ * l).1 = (N : AF F) • idem F v • u l.1 := fun l => by
      rw [hu, hu, ← smul_assoc, ← smul_assoc, ← smul_assoc]
      congr 1
      have q : algebraMap (AF F) (AE F E) (idem F v) * algebraMap (AF F) (AE F E) (idem F v) =
          algebraMap (AF F) (AE F E) (idem F v) := by rw [← map_mul, idem_sq]
      rw [Subgroup.coe_mul, Units.val_mul, map_mul, hl₀, map_add, map_smul, map_smul, map_natCast, map_one]
      simp only [Algebra.smul_def, smul_eq_mul, map_mul, map_sub, map_one, map_natCast, Algebra.algebraMap_self, RingHom.id_apply]
      linear_combination ((N : AE F E) * c l.1.1 - c l.1.1) * q
    have h0 : (0 : ℝ) < absE F E l₀.1 := by
      refine lt_of_le_of_ne NNReal.zero_le_coe fun e => ?_
      have : absE F E l₀.1 * absE F E l₀.1⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      rw [show absE F E l₀.1 = 0 from NNReal.coe_eq_zero.1 e.symm, zero_mul] at this
      exact zero_ne_one this
    refine Integrable.mono' (((hint.comp_mul_left l₀).norm.const_mul (((absE F E l₀.1 : ℝ) ^ z)⁻¹)).integrableOn)
      ((cont_wt hν z).comp continuous_subtype_val).aestronglyMeasurable
      (ae_restrict_of_forall_mem (hG.isClosed_fiber 0).measurableSet.compl fun l hl => ?_)
    have := (hin v (l₀ * l).1).1 (e3 l ▸ hk _ hl)
    rw [if_pos this, one_mul, norm_wt, norm_wt, Subgroup.coe_mul, map_mul, NNReal.coe_mul, mul_pow,
      inv_mul_cancel_left₀ (pow_pos h0 z).ne']

theorem finCone2_of (hI : IdeleFub) (hJ : IdealId0) (hS : StabEx) : FinCone2 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e u ei ev hc h v
  obtain ⟨V₀, V₁, c, hu, h00, h11, hinv, hcomp⟩ := dirs hc
  have hv := (hc.good.vac v).1
  have e2 : ∀ l, idem F v • u l = (idem F v • c l.1) • V₀ := fun l => by rw [hu, smul_assoc]
  have c2 : ∀ l, idem F v • u l ∈ latAtV X W v → Acts (evFin F v) (M.co.rho B.ψ (idem F v • u l)) (M.vac v) (M.vac v) :=
    fun l hl => vac_fix hc.good hl (by rw [e2, hh_smul, h00, mul_zero])
  refine ⟨fun l => ?_, c2, fun K m hK hm χX χW om r s r' s' hP ν z hν hz => ?_⟩
  · split_ifs with hl
    · rw [opF_eq hv hv (c2 l hl), (h.vac v).1]
    · rw [opF_eq hv (rv_sb hc.base M v _ hv) (rv_acts B M (at_idem v _) _)]
      by_contra hne
      rw [e2] at hne hl
      have := key hc h hinv (hcomp v) hv 1 (fun t ht => by
        rw [one_smul]
        exact acts_uniq hv (rv_acts B M ((latAtV_at_stable X W v).1 _ ht) _)
          (vac_fix hc.good ht (by rw [hh_smul, h11, mul_zero]))) _ (e2 l ▸ at_idem v _) hne
      rw [one_smul] at this
      exact hl this
  obtain ⟨ω, ρ, L⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ n d B X W M om
    ⟨hP.base, ⟨r, s, hP.herm⟩, ⟨r', s', hP.skew⟩, hP.good, χX, χW, hP.weil⟩ v
  obtain ⟨K', -, -, hK', hKc, -⟩ := hS F E σ B n X r s hP.base hP.herm
  obtain rfl : K = K' := Subgroup.ext fun g => (hK g).trans (hK' g).symm
  haveI := kAt_compact hKc v
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : IsProbabilityMeasure (m.kf v) := ⟨(hm.kf v).2⟩
  have o1 : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := (uSub σ W v).one_mem
  have sb : ∀ k : kAt K (evFin F v), ∀ φ ∈ SB _, ω (k.1, 1) φ ∈ SB _ := fun k φ hφ => L.pres _ (kAt_mem k) _ o1 φ hφ
  have op : ∀ (k : kAt K (evFin F v)) (l : (AE F E)ˣ), ∀ φ ∈ SB _,
      opF v (fun Φ => M.co.rho B.ψ (idem F v • u l) (om (k.1, 1) Φ)) φ = rv B M v (idem F v • u l) (ω (k.1, 1) φ) :=
    fun k l φ hφ => opF_eq hφ (rv_sb hc.base M v _ (sb k φ hφ)) (acts_comp ((IsUWeilPair.isUSplitting hP.weil).pres _)
      ((L.acts _ (kAt_mem k) _ o1 φ hφ _).2 rfl) (rv_acts B M (at_idem v _) _))
  let A : Fl F v n d → Fl F v n₁ d₁ := fun φ y => @integral _ _ _ _ (borel _) (m.xf v) fun l =>
    ev v (rv B M v (idem F v • u l.1) φ) y * wt ν z l.1
  have hA := fun φ (hφ : φ ∈ SB _) => tate hI hJ hS hc h v m hm hν hz (φ := φ) hφ
  have lc : ∀ φ ∈ SB _, IsLocallyConstant fun k : kAt K (evFin F v) => ω (k.1, 1) φ := fun φ hφ => by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun k₀ => ?_
    obtain ⟨U, hU, hU'⟩ := (PositivityTheory.ThKF0.actsEx F E σ B n d X W M χX χW om r s r' s' hP v).2.2 _ (sb k₀ φ hφ)
    have t : Tendsto (fun k : kAt K (evFin F v) => (((k * k₀⁻¹).1, 1) : UA σ X.J × UA σ W.J)) (𝓝 k₀) (𝓝 1) := by
      have : Continuous fun k : kAt K (evFin F v) => (((k * k₀⁻¹).1, 1) : UA σ X.J × UA σ W.J) :=
        (continuous_subtype_val.comp (continuous_mul_const k₀⁻¹)).prodMk continuous_const
      have := this.tendsto k₀
      rwa [mul_inv_cancel] at this
    filter_upwards [t.eventually hU] with k hk
    have h1 := (L.acts _ (kAt_mem (k * k₀⁻¹)) _ o1 _ (sb k₀ φ hφ) _).1 (hU' _ hk (kAt_mem (k * k₀⁻¹)) o1)
    rw [← L.mul _ (kAt_mem (k * k₀⁻¹)) _ o1 _ (kAt_mem k₀) _ o1 φ hφ, mul_one, ← Subgroup.coe_mul, inv_mul_cancel_right] at h1
    exact h1.symm
  have hk : ∀ φ ∈ SB _, (∀ y, Integrable (fun k : kAt K (evFin F v) => A (ω (k.1, 1) φ) y * 1) (m.kf v)) ∧
      (fun y => ∫ k : kAt K (evFin F v), A (ω (k.1, 1) φ) y * 1 ∂(m.kf v)) ∈ SB _ := fun φ hφ =>
    int_fin (m.kf v) (fun k => A (ω (k.1, 1) φ)) (fun _ => 1) ((lc φ hφ).comp A).range_finite
      (fun a => (((lc φ hφ).comp A).isOpen_fiber a).measurableSet) Set.univ (fun a ha => absurd trivial ha)
      (integrable_const _).integrableOn _ fun k => (hA _ (sb k φ hφ)).2
  simp only [mul_one] at hk
  have ce : ∀ φ ∈ SB _, coneF B M om m v (ev v) u ν z φ = fun y => ∫ k : kAt K (evFin F v), A (ω (k.1, 1) φ) y ∂(m.kf v) :=
    fun φ hφ => funext fun y => by
      simp only [coneF, op _ _ φ hφ, A, wt, mul_assoc]
  have Al : ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ (a : ℂ) y, A (φ + a • φ') y = A φ y + a * A φ' y := fun φ hφ φ' hφ' a y => by
    letI : MeasurableSpace (idAt E (evFin F v)) := borel _
    simp only [A, rv, schr_lin, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
    rw [integral_add ((hA φ hφ).1 y) (((hA φ' hφ').1 y).const_mul a), integral_const_mul]
  have cl : ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ a : ℂ, coneF B M om m v (ev v) u ν z (φ + a • φ') =
      coneF B M om m v (ev v) u ν z φ + a • coneF B M om m v (ev v) u ν z φ' := fun φ hφ φ' hφ' a => by
    rw [ce _ hφ, ce _ hφ', ce _ (add_mem hφ (Submodule.smul_mem _ a hφ'))]
    funext y
    simp only [map_add, map_smul, Al _ (sb _ φ hφ) _ (sb _ φ' hφ'), Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add ((hk φ hφ).1 y) (((hk φ' hφ').1 y).const_mul a), integral_const_mul]
  have c0 : coneF B M om m v (ev v) u ν z 0 = 0 := by
    have := cl 0 (zero_mem _) 0 (zero_mem _) 1
    rw [one_smul, one_smul, add_zero] at this
    exact left_eq_add.1 this
  let Λ₀ : SB (Fin n × Fin d → Fv F v) →ₗ[ℂ] Fl F v n₁ d₁ :=
    { toFun := fun φ => coneF B M om m v (ev v) u ν z φ.1
      map_add' := fun φ φ' => by simpa using cl _ φ.2 _ φ'.2 1
      map_smul' := fun a φ => by simpa [c0] using cl 0 (zero_mem _) _ φ.2 a }
  obtain ⟨Λ, hΛ⟩ := Λ₀.exists_extend
  refine ⟨Λ, fun φ hφ => ?_⟩
  have eΛ : Λ φ = coneF B M om m v (ev v) u ν z φ := LinearMap.congr_fun hΛ ⟨φ, hφ⟩
  refine ⟨eΛ, by rw [eΛ, ce φ hφ]; exact (hk φ hφ).2, fun y => ⟨fun k => ?_, ?_⟩⟩
  · simp only [op _ _ φ hφ]
    exact (hA _ (sb k φ hφ)).1 y
  · simp only [op _ _ φ hφ]
    exact (hk φ hφ).1 y

end PositivityTheory.ThKG.Loc.Cone.Fin

end
