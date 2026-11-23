import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.MemOfProjTwoEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropASt

namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex NumberField
open scoped InnerProductSpace

noncomputable section

namespace Col

theorem extend_hom {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (N : Submodule ℤ M) (hsat : ∀ (k : ℤ) (x : M), k ≠ 0 → k • x ∈ N → x ∈ N) (ψ : N →ₗ[ℤ] ℤ) :
    ∃ Ψ : M →ₗ[ℤ] ℤ, ∀ x : N, Ψ x = ψ x := by
  have : IsAddTorsionFree (M ⧸ N) := by
    refine ⟨fun n hn a b hab => ?_⟩
    induction a using Submodule.Quotient.induction_on with | H x => ?_
    induction b using Submodule.Quotient.induction_on with | H y => ?_
    simp only at hab
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hab
    rw [Submodule.Quotient.eq]
    refine hsat n (x - y) (by exact_mod_cast hn) ?_
    rw [natCast_zsmul, smul_sub]; exact hab
  have : Module.Free ℤ (M ⧸ N) := Module.free_of_finite_type_torsion_free'
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property N.mkQ (LinearMap.id) (Submodule.mkQ_surjective N)
  have hmem : ∀ x : M, x - σ (N.mkQ x) ∈ N := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub]
    have := LinearMap.congr_fun hσ (N.mkQ x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this, sub_self]
  let p : M →ₗ[ℤ] N := LinearMap.codRestrict N (LinearMap.id - σ ∘ₗ N.mkQ) (fun x => hmem x)
  refine ⟨ψ ∘ₗ p, fun x => ?_⟩
  have : p x = x := by
    apply Subtype.ext
    simp [p, (Submodule.Quotient.mk_eq_zero N).2 x.2]
  simp [this]

variable {E : Type} [Field E] [NumberField E]

def GB (X : PT E) (I : Submodule ℤ (Vsp X.dim)) : Submodule ℤ (EuclideanSpace ℂ (Fin (gB (IR I)))) :=
  (Ip X I).map (((wmap (IR I)).toLinearMap).restrictScalars ℤ)

theorem mem_GB {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {t : EuclideanSpace ℂ (Fin (gB (IR I)))} :
    t ∈ GB X I ↔ ∃ x ∈ Ip X I, wmap (IR I) x = t := by
  unfold GB
  rw [Submodule.mem_map]
  rfl

theorem wmap_mem_GB {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {x : Vsp X.dim} (hx : x ∈ Ip X I) :
    wmap (IR I) x ∈ GB X I := mem_GB.2 ⟨x, hx, rfl⟩

section GBsec

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
include hI

theorem GB_norm {t : EuclideanSpace ℂ (Fin (gB (IR I)))} (ht : t ∈ GB X I) (h0 : t ≠ 0) :
    P.th ≤ ‖t‖ := by
  obtain ⟨x, hx, rfl⟩ := mem_GB.1 ht
  rw [norm_wmap (hK_of hI)]
  by_cases hxI : x ∈ I
  · exfalso; apply h0
    rw [← norm_eq_zero, norm_wmap (hK_of hI), proj_two_of_mem (hK_of hI) (mem_IR hxI), norm_zero]
  · exact gap_le_norm_proj_two hI hx hxI

theorem GB_discrete : DiscreteTopology (GB X I) := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have : ({0} : Set (GB X I)) = Subtype.val ⁻¹' Metric.ball 0 P.th := by
    ext ⟨t, ht⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    constructor
    · intro h
      have : t = 0 := congrArg Subtype.val h
      rw [this, norm_zero]; exact th_pos P
    · intro h
      by_contra hne
      have h0 : t ≠ 0 := fun h' => hne (Subtype.ext h')
      exact absurd (GB_norm hI ht h0) (not_le.2 h)
  rw [this]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

theorem GB_span (hP : Ext.PackingCount) :
    Submodule.span ℝ (GB X I : Set (EuclideanSpace ℂ (Fin (gB (IR I))))) = ⊤ := by
  have hK := hK_of hI
  set C0 := ∑ i, ‖X.b i‖ with hC0
  have hC0n : 0 ≤ C0 := Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨M, hM0, hM⟩ := reps_bdd hI hP C0
  have approx : ∀ t, ∃ s ∈ GB X I, ‖t - s‖ ≤ C0 + M := by
    intro t
    set v := jj (IR I) t
    set γ : Vsp X.dim := (ZSpan.floor X.b v : Vsp X.dim)
    have hγ : γ ∈ X.L := (ZSpan.floor X.b v).2
    have hvγ : ‖v - γ‖ ≤ C0 := by
      rw [← ZSpan.fract_apply]; exact ZSpan.norm_fract_le _ _
    have hucv : uc (IR I) v = 0 := by simp [uc, v, z_jj]
    have huc : ‖uc (IR I) γ‖ ≤ C0 := by
      have : uc (IR I) γ = -uc (IR I) (v - γ) := by rw [uc_sub, hucv]; simp
      rw [this, norm_neg]
      exact (norm_uc_le hI.iso _).trans hvγ
    obtain ⟨y', hy'L, hy'u, hy'M⟩ := hM γ hγ huc
    have hIp : γ - y' ∈ Ip X I := by
      refine ⟨X.L.sub_mem hγ hy'L, fun a ha => ?_⟩
      rw [← (isU_uc (I := I) (γ - y')).2 a (mem_IR ha), uc_sub, hy'u, sub_self, inner_zero_left]
    refine ⟨wmap (IR I) (γ - y'), wmap_mem_GB hIp, ?_⟩
    have ht : t = wmap (IR I) v := (wmap_jj _ t).symm
    have : t - wmap (IR I) (γ - y') = wmap (IR I) (v - γ) + wmap (IR I) y' := by
      rw [ht, ← map_sub, ← map_add]; congr 1; abel
    rw [this]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_wmap hK]; exact (norm_proj_two_le hK _).trans hvγ
    · rw [norm_wmap hK]; exact hy'M
  by_contra hW
  rw [← Submodule.orthogonal_eq_bot_iff] at hW
  obtain ⟨t0, ht0, ht0ne⟩ := (Submodule.ne_bot_iff _).1 hW
  have hn0 : 0 < ‖t0‖ := norm_pos_iff.2 ht0ne
  set c : ℝ := (C0 + M + 1) / ‖t0‖
  set t := c • t0
  have htW : t ∈ (Submodule.span ℝ (GB X I : Set (EuclideanSpace ℂ (Fin (gB (IR I))))))ᗮ :=
    Submodule.smul_mem _ _ ht0
  have hnt : ‖t‖ = C0 + M + 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [c]; field_simp
  obtain ⟨s, hs, hts⟩ := approx t
  have hin : ⟪s, t⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span hs) htW
  have h2 := norm_sub_sq_real t s
  rw [real_inner_comm, hin] at h2
  have : ‖t‖ ^ 2 ≤ ‖t - s‖ ^ 2 := by nlinarith [sq_nonneg ‖s‖]
  have h3 : ‖t - s‖ < ‖t‖ := by rw [hnt]; linarith
  nlinarith [norm_nonneg (t - s), norm_nonneg t]

end GBsec

section GBsec2

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
include hI

theorem GB_perfect (φ : GB X I →+ ℤ) :
    ∃ x0 ∈ Ip X I, ∀ x (hx : x ∈ Ip X I),
      (φ ⟨wmap (IR I) x, wmap_mem_GB hx⟩ : ℝ) = (Hf (wmap (IR I) x0) (wmap (IR I) x)).im := by
  have hK := hK_of hI
  set N : Submodule ℤ X.L := (Ip X I).comap X.L.subtype with hN
  have hsat : ∀ (k : ℤ) (x : X.L), k ≠ 0 → k • x ∈ N → x ∈ N := by
    intro k x hk hx
    refine ⟨x.2, fun a ha => ?_⟩
    have h := hx.2 a ha
    simp only [Submodule.coe_subtype, Submodule.coe_smul] at h
    rw [← Int.cast_smul_eq_zsmul ℂ, Hf_smul_l, Complex.mul_im] at h
    simp only [Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero, mul_eq_zero,
      Int.cast_eq_zero] at h
    rcases h with h | h
    · exact absurd h hk
    · exact h
  let ψ0 : N →+ GB X I :=
    { toFun := fun x => ⟨wmap (IR I) ((x : X.L) : Vsp X.dim), wmap_mem_GB x.2⟩
      map_zero' := by ext1; simp
      map_add' := by intro x y; ext1; simp }
  obtain ⟨Ψ, hΨ⟩ := extend_hom N hsat (φ.comp ψ0).toIntLinearMap
  obtain ⟨x0, hx0L, hx0⟩ := X.perfect Ψ.toAddMonoidHom
  have hx0I : x0 ∈ Ip X I := by
    refine ⟨hx0L, fun a ha => ?_⟩
    have haIp : a ∈ Ip X I := ⟨hI.le ha, fun b hb => hI.iso a ha b hb⟩
    have h1 := hx0 ⟨a, hI.le ha⟩
    have h2 := hΨ ⟨⟨a, hI.le ha⟩, haIp⟩
    have hw : wmap (IR I) a = 0 := by
      rw [← norm_eq_zero, norm_wmap hK, proj_two_of_mem hK (mem_IR ha), norm_zero]
    have h3 : ψ0 ⟨⟨a, hI.le ha⟩, haIp⟩ = 0 := Subtype.ext hw
    simp only [LinearMap.toAddMonoidHom_coe] at h1
    rw [h2] at h1
    simp only [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_comp, Function.comp_apply, h3,
      map_zero, Int.cast_zero] at h1
    exact h1.symm
  refine ⟨x0, hx0I, fun x hx => ?_⟩
  have h1 := hx0 ⟨x, hx.1⟩
  have h2 := hΨ ⟨⟨x, hx.1⟩, hx⟩
  simp only [LinearMap.toAddMonoidHom_coe] at h1
  rw [h2] at h1
  rw [Hf_wmap hK, herm_im_proj_two hI hx0I hx]
  exact h1

end GBsec2

def bB {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
    (hP : Ext.PackingCount) :
    Module.Basis (Fin (2 * Fintype.card (Fin (gB (IR I))))) ℝ (EuclideanSpace ℂ (Fin (gB (IR I)))) :=
  haveI := GB_discrete hI
  haveI : IsZLattice ℝ (GB X I) := ⟨GB_span hI hP⟩
  haveI := ZLattice.module_free ℝ (GB X I)
  (Module.Basis.ofZLatticeBasis ℝ (GB X I) (Module.Free.chooseBasis ℤ (GB X I))).reindex
    (Fintype.equivFinOfCardEq (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ, finrank_real_of_complex,
        finrank_euclideanSpace]))

theorem lat_bB {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
    (hP : Ext.PackingCount) : lat (bB hI hP) = GB X I := by
  haveI := GB_discrete hI
  haveI : IsZLattice ℝ (GB X I) := ⟨GB_span hI hP⟩
  haveI := ZLattice.module_free ℝ (GB X I)
  rw [lat, bB, Module.Basis.range_reindex, Module.Basis.ofZLatticeBasis_span]

theorem exp_sign (q : ℕ) (k : ℤ) :
    cexp (-(Real.pi * q * (k : ℝ)) * I) = (((-1 : ℝ) ^ k : ℝ) : ℂ) ^ q := by
  have e1 : (-(Real.pi * q * (k : ℝ)) * I : ℂ) = ((-(Real.pi * q * k) : ℝ) : ℂ) * I := by push_cast; ring
  have e2 : Real.pi * q * k = ((q * k : ℤ) : ℝ) * Real.pi := by push_cast; ring
  rw [e1, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, e2,
    Real.cos_int_mul_pi, Real.sin_int_mul_pi, neg_zero, Complex.ofReal_zero, zero_mul, add_zero,
    ← Complex.ofReal_pow]
  congr 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm]

open Classical in

def kaB (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (q : ℕ) (t : EuclideanSpace ℂ (Fin (gB (IR I)))) : ℂ :=
  if h : ∃ x ∈ Ip X I, wmap (IR I) x = t then (X.eps h.choose : ℂ) ^ q else 1

section GT

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
include hI

theorem kaB_wmap (q : ℕ) {x : Vsp X.dim} (hx : x ∈ Ip X I) : kaB X I q (wmap (IR I) x) = (X.eps x : ℂ) ^ q := by
  have h : ∃ x' ∈ Ip X I, wmap (IR I) x' = wmap (IR I) x := ⟨x, hx, rfl⟩
  rw [kaB, dif_pos h]
  have hs := h.choose_spec
  have hp : p2 (IR I) h.choose = p2 (IR I) x := by
    rw [← jj_wmap' (hK_of hI), ← jj_wmap' (hK_of hI) x, hs.2]
  rw [sign_eq_of_proj_two_eq hI hs.1 hx hp]

variable (hP : Ext.PackingCount)

def YB (q : ℕ) : GT (Fin (gB (IR I))) where
  b := bB hI hP
  integral := by
    intro x y hx hy
    rw [lat_bB] at hx hy
    obtain ⟨x', hx', rfl⟩ := mem_GB.1 hx
    obtain ⟨y', hy', rfl⟩ := mem_GB.1 hy
    rw [Hf_wmap (hK_of hI), herm_im_proj_two hI hx' hy']
    exact X.integral x' y' hx'.1 hy'.1
  perfect := by
    intro φ
    have hl := lat_bB hI hP
    let ι0 : GB X I →+ lat (bB hI hP) :=
      { toFun := fun t => ⟨t.1, by rw [hl]; exact t.2⟩, map_zero' := rfl, map_add' := fun _ _ => rfl }
    obtain ⟨x0, hx0, h0⟩ := GB_perfect hI (φ.comp ι0)
    refine ⟨wmap (IR I) x0, by rw [hl]; exact wmap_mem_GB hx0, fun y => ?_⟩
    have hyG : (y : EuclideanSpace ℂ (Fin (gB (IR I)))) ∈ GB X I := (le_of_eq hl) y.2
    obtain ⟨x, hx, hxy⟩ := mem_GB.1 hyG
    have := h0 x hx
    have hy : ι0 ⟨wmap (IR I) x, wmap_mem_GB hx⟩ = y := Subtype.ext hxy
    rw [AddMonoidHom.comp_apply, hy] at this
    rw [this, hxy]
  ka := kaB X I q
  ka_abs := by
    intro t ht
    rw [lat_bB] at ht
    obtain ⟨x, hx, rfl⟩ := mem_GB.1 ht
    rw [kaB_wmap hI _ hx, norm_pow]
    rcases X.eps_pm x hx.1 with h | h <;> simp [h]

theorem YB_lat (q : ℕ) {t : EuclideanSpace ℂ (Fin (gB (IR I)))} : t ∈ lat (YB hI hP q).b ↔ t ∈ GB X I := by
  show t ∈ lat (bB hI hP) ↔ t ∈ GB X I
  rw [lat_bB]

theorem YB_ka (q : ℕ) {x : Vsp X.dim} (hx : x ∈ Ip X I) : (YB hI hP q).ka (wmap (IR I) x) = (X.eps x : ℂ) ^ q := kaB_wmap hI q hx

theorem YB_coc (q : ℕ) : (YB hI hP q).Coc q := by
  intro γ hγ γ' hγ'
  rw [YB_lat] at hγ hγ'
  obtain ⟨x, hx, rfl⟩ := mem_GB.1 hγ
  obtain ⟨y, hy, rfl⟩ := mem_GB.1 hγ'
  have hxy : x + y ∈ Ip X I := (Ip X I).add_mem hx hy
  obtain ⟨k, hk⟩ := X.integral x y hx.1 hy.1
  rw [← map_add, YB_ka hI hP q hxy, YB_ka hI hP q hx, YB_ka hI hP q hy, Hf_wmap (hK_of hI),
    herm_im_proj_two hI hx hy, hk, exp_sign]
  have he := X.eps_add x hx.1 y hy.1
  rw [hk, show Real.pi * (k : ℝ) = (k : ℝ) * Real.pi by ring, Real.cos_int_mul_pi] at he
  have hc : (X.eps (x + y) : ℂ) = (X.eps x : ℂ) * X.eps y * (((-1 : ℝ) ^ k : ℝ) : ℂ) := by
    have := congrArg (fun r : ℝ => (r : ℂ)) he
    push_cast at this ⊢
    exact this
  rw [hc, mul_pow, mul_pow]

end GT

end Col

end

end ReciprocityTheory.ChartRestriction.G.I2
