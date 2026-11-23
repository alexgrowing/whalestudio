import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.SchurTraceOfHomInv
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.InvInv
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.InvInt

namespace Formalism.InvariantFactorPaths.PW

open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames

section gen

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}

theorem wl_pow_coe (G : GlW K V n) (U : Submodule K V) (hU : G.Stable U) (a b : Fin n) (k : ℕ) (x : U) :
    ((((res G U hU).E a b ^ k) x : U) : V) = (G.E a b ^ k) (x : V) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    exact congrArg (G.E a b) ih

theorem wl_iso_stable (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) : G.Stable (IsoW G W la) :=
  G.gS_stable _

theorem wl_iso_le (G : GlW K V n) {W : Submodule K V} (hW : G.Stable W) (la : Fin n → ℤ) : IsoW G W la ≤ W :=
  G.gS_le (fun _ hv => hv.2) hW

theorem wl_iso_le_iSup (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) :
    IsoW G W la ≤ ⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)} :=
  G.gS_le (fun v hv => Submodule.mem_iSup_of_mem (⟨v, hv⟩ : {v : V // G.IsHW la v ∧ v ∈ W})
    (G.subset_gS _ (Set.mem_singleton v))) (GlX.iSup_stable G fun _ => G.gS_stable _)

theorem wl_iso_wt (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) {x : V} (hx : x ∈ IsoW G W la)
    {ν : Fin n → ℤ} (hν : ¬ Dle ν la) : G.comp ν x = 0 := by
  refine Submodule.iSup_induction _ (motive := fun x => G.comp ν x = 0) (wl_iso_le_iSup G W la hx)
    (fun v y hy => ?_) (by simp) (fun y z hy hz => by rw [map_add, hy, hz, add_zero])
  by_contra h
  exact hν (G.wt_le_of_mem v.2.1 hy h)

theorem wl_comp_hw (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) {x : V} (hx : x ∈ IsoW G W la) :
    G.IsHW la (G.comp la x) := by
  refine ⟨G.isWt_comp la x, fun a b hab => ?_⟩
  have e := G.shift a b (la + dl a b) x
  rw [add_sub_cancel_right] at e
  rw [← e]
  refine wl_iso_wt G W la (G.gS_stable _ a b x hx) (fun hle => ?_)
  have := Dle_antisymm hle (Dle_raise la hab)
  exact dl_ne_zero (ne_of_lt hab) (by simpa using this)

theorem wl_comp_comm {U : Type} [AddCommGroup U] [Module K U] (G₁ : GlW K U n) (G₂ : GlW K V n) (θ : U →ₗ[K] V)
    (hθ : ∀ c x, θ (G₁.E c c x) = G₂.E c c (θ x)) (μ : Fin n → ℤ) (x : U) :
    θ (G₁.comp μ x) = G₂.comp μ (θ x) := by
  classical
  have hwt : ∀ ν, G₂.IsWt ν (θ (G₁.comp ν x)) := fun ν => GlX.isWt_of_eig G₂ (fun c => by
    rw [← hθ, G₁.diag, map_smul])
  obtain ⟨S, hS⟩ := G₁.dec x
  have hx' := G₁.sum_comp x (insert μ S) (fun ν hν => hS ν (fun h => hν (Finset.mem_insert_of_mem h)))
  conv_rhs => rw [← hx']
  rw [map_sum, map_sum, Finset.sum_eq_single μ (fun ν _ hν => by rw [G₂.comp_of_isWt (hwt ν), if_neg (Ne.symm hν)])
    (fun h => absurd (Finset.mem_insert_self μ S) h), G₂.comp_of_isWt (hwt μ), if_pos rfl]

theorem wl_transport (G : GlW K V n) {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {la : Fin n → ℤ}
    {h h' : V} (hh : G.IsHW la h) (hh' : G.IsHW la h') (hhW : h ∈ W) (hh'W : h' ∈ W) (h0 : h ≠ 0) :
    ∃ θ : G.gS {h} →ₗ[K] V, (∀ a b x, θ ((res G _ (G.gS_stable {h})).E a b x) = G.E a b (θ x)) ∧
      (∀ y, θ y ∈ G.gS {h'}) ∧ ∀ m ∈ G.gS {h'}, ∃ y, θ y = m := by
  have hk := GlX.ker_le G hW hWf hh hh' hhW hh'W h0
  refine ⟨GlX.tr G hk ∘ₗ (LinearEquiv.ofEq _ _ (GlX.range_Lv G h).symm).toLinearMap, fun a b x => ?_, fun y => ?_,
    fun m hm => ?_⟩
  · exact GlX.tr_E G hk a b (LinearEquiv.ofEq _ _ (GlX.range_Lv G h).symm x) _
  · rw [← GlX.range_Lv]
    exact GlX.tr_mem G hk _
  · rw [← GlX.range_Lv] at hm
    obtain ⟨c, rfl⟩ := hm
    refine ⟨⟨GlX.Lv G h c, by rw [← GlX.range_Lv]; exact LinearMap.mem_range_self _ c⟩, ?_⟩
    exact GlX.tr_apply G hk c

theorem wl_trace (G : GlW K V n) {la : Fin n → ℤ} {h : V} (hh : G.IsHW la h) (h0 : h ≠ 0)
    [FiniteDimensional K (G.gS {h})] :
    LinearMap.trace K _ ((res G _ (G.gS_stable {h})).comp la) = 1 := by
  have hmem : h ∈ G.gS {h} := G.subset_gS {h} rfl
  have hp : LinearMap.IsProj (K ∙ (⟨h, hmem⟩ : G.gS {h})) ((res G _ (G.gS_stable {h})).comp la) := by
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · obtain ⟨c, hc⟩ := G.comp_top_of_mem hh x.2
      exact Submodule.mem_span_singleton.mpr ⟨c, Subtype.ext hc.symm⟩
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [map_smul]
      congr 1
      exact Subtype.ext hh.1
  rw [hp.trace, finrank_span_singleton (fun e => h0 (congrArg Subtype.val e)), Nat.cast_one]

def topC (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) : IsoW G W la →ₗ[K] V :=
  G.comp la ∘ₗ (IsoW G W la).subtype

theorem wl_key (hNat : InvNat) (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) (l : ℕ) {h : V}
    (hh : G.IsHW la h) (h0 : h ≠ 0) [FiniteDimensional K (G.gS {h})]
    (hSch : ∀ φ : (G.gS {h}) →ₗ[K] (G.gS {h}),
      (∀ c, homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E c c φ = 0) →
      InvOp (homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E) l (List.finRange n) φ =
        (LinearMap.trace K _ φ / (Module.finrank K (G.gS {h}) : K)) • LinearMap.id)
    (θ : G.gS {h} →ₗ[K] V) (hθ : ∀ a b x, θ ((res G _ (G.gS_stable {h})).E a b x) = G.E a b (θ x))
    (hθY : ∀ y, θ y ∈ IsoW G W la) (y : G.gS {h}) :
    InvOp (homAct (res G (IsoW G W la) (wl_iso_stable G W la)).E G.E) l (List.finRange n) (topC G W la) ⟨θ y, hθY y⟩ =
      ((Module.finrank K (G.gS {h}) : K))⁻¹ • θ y := by
  have e1 := hNat K (IsoW G W la →ₗ[K] V) (G.gS {h} →ₗ[K] V) (Fin n)
    (homAct (res G (IsoW G W la) (wl_iso_stable G W la)).E G.E) (homAct (res G _ (G.gS_stable {h})).E G.E)
    (LinearMap.lcomp K V (θ.codRestrict (IsoW G W la) hθY))
    (fun a b φ => homAct_precomp (res G (IsoW G W la) (wl_iso_stable G W la)).E (res G _ (G.gS_stable {h})).E G.E
      (θ.codRestrict (IsoW G W la) hθY) (fun a b x => Subtype.ext (hθ a b x)) a b φ)
    l (List.finRange n) (topC G W la)
  have e2 := hNat K (G.gS {h} →ₗ[K] G.gS {h}) (G.gS {h} →ₗ[K] V) (Fin n)
    (homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E) (homAct (res G _ (G.gS_stable {h})).E G.E)
    (LinearMap.llcomp K _ _ V θ)
    (fun a b φ => homAct_postcomp (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E G.E θ hθ a b φ)
    l (List.finRange n) ((res G _ (G.gS_stable {h})).comp la)
  have e3 : LinearMap.lcomp K V (θ.codRestrict (IsoW G W la) hθY) (topC G W la) =
      LinearMap.llcomp K _ _ V θ ((res G _ (G.gS_stable {h})).comp la) := by
    ext x
    exact (wl_comp_comm (res G _ (G.gS_stable {h})) G θ (fun c x => hθ c c x) la x).symm
  have h0' : ∀ c, homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E c c
      ((res G _ (G.gS_stable {h})).comp la) = 0 := by
    intro c
    ext x
    rw [homAct_apply, (res G _ (G.gS_stable {h})).diag, (res G _ (G.gS_stable {h})).comp_Ecc, sub_self]
    rfl
  rw [e3, ← e2, hSch _ h0', wl_trace G hh h0, map_smul, one_div] at e1
  exact LinearMap.congr_fun e1 y

end gen

section padic

variable (p : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[p] V] {n : ℕ}

theorem subset_deltaLat (G : GlW ℚ_[p] V n) (s : Set V) : s ⊆ DeltaLat p G s := by
  intro x hx
  rw [SetLike.mem_coe, DeltaLat, AddSubgroup.mem_sInf]
  exact fun L hL => hL.1 hx

theorem deltaLat_closed (G : GlW ℚ_[p] V n) (s : Set V) : ZpClosed p (DeltaLat p G s) := by
  intro c hc x hx
  rw [DeltaLat, AddSubgroup.mem_sInf] at hx ⊢
  exact fun L hL => hL.2.1 c hc x (hx L hL)

theorem deltaLat_div (G : GlW ℚ_[p] V n) (s : Set V) : DivStable G.E (DeltaLat p G s) := by
  intro a b hab k x hx
  rw [DeltaLat, AddSubgroup.mem_sInf] at hx ⊢
  exact fun L hL => hL.2.2 a b hab k x (hx L hL)

end padic

theorem weylInt_of (hNat : InvNat) (hSchur : SchurTrace) : WeylInt := by
  intro p _ V _ _ n G W M l D la x hx hxM
  by_cases hex : ∃ h, G.IsHW la h ∧ h ∈ W ∧ h ≠ 0
  swap
  · push Not at hex
    have hbot : IsoW G W la ≤ ⊥ := G.gS_le (fun v hv => by
      rw [SetLike.mem_coe, Submodule.mem_bot]; exact hex v hv.1 hv.2) G.bot_stable
    rw [(Submodule.mem_bot _).mp (hbot hx), smul_zero]
    exact AddSubgroup.zero_mem _
  obtain ⟨h, hh, hhW, h0⟩ := hex
  have hUW : G.gS {h} ≤ W := G.gS_le (by simpa using hhW) D.stable
  have := D.fd
  have : FiniteDimensional ℚ_[p] (G.gS {h}) := Submodule.finiteDimensional_of_le hUW
  have hmem : h ∈ G.gS {h} := G.subset_gS {h} rfl
  have : Nontrivial (G.gS {h}) := ⟨⟨⟨h, hmem⟩, 0, fun e => h0 (congrArg Subtype.val e)⟩⟩
  have hfr : (Module.finrank ℚ_[p] (G.gS {h}) : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ_[p]) (M := G.gS {h})).ne'
  set Δ := DeltaLat p G {h | G.IsHW la h ∧ h ∈ W ∧ h ∈ M} with hΔ
  have hΔZ : ZpClosed p Δ := deltaLat_closed p G _
  have hΔD : DivStable G.E Δ := deltaLat_div p G _

  have hid : ∀ z : IsoW G W la,
      InvOp (homAct (res G (IsoW G W la) (wl_iso_stable G W la)).E G.E) l (List.finRange n) (topC G W la) z =
        ((Module.finrank ℚ_[p] (G.gS {h}) : ℚ_[p]))⁻¹ • (z : V) := by
    have hle : (⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)}) ≤
        Submodule.map (IsoW G W la).subtype (LinearMap.eqLocus
          (InvOp (homAct (res G (IsoW G W la) (wl_iso_stable G W la)).E G.E) l (List.finRange n) (topC G W la))
          (((Module.finrank ℚ_[p] (G.gS {h}) : ℚ_[p]))⁻¹ • (IsoW G W la).subtype)) := by
      refine iSup_le fun v m hm => ?_
      obtain ⟨θ, hθ, hθm, hsur⟩ := wl_transport G D.stable D.finW hh v.2.1 hhW v.2.2 h0
      have hvY : G.gS {(v : V)} ≤ IsoW G W la :=
        G.gS_le (by
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact G.subset_gS _ v.2) (G.gS_stable _)
      obtain ⟨y, rfl⟩ := hsur m hm
      exact ⟨⟨θ y, hvY (hθm y)⟩, wl_key hNat G W la l hh h0
        (fun φ hφ => hSchur ℚ_[p] V n G W l D.stable D.fd D.finW D.bound la h hh hhW h0 φ hφ) θ hθ
        (fun y => hvY (hθm y)) y, rfl⟩
    intro z
    obtain ⟨z', hz', hzz⟩ := hle (wl_iso_le_iSup G W la z.2)
    have : z' = z := Subtype.ext hzz
    rw [← this]
    exact hz'

  have hLd : DivStable (res G (IsoW G W la) (wl_iso_stable G W la)).E (M.comap (IsoW G W la).subtype.toAddMonoidHom) := by
    intro a b hab j y hy
    show ((((j.factorial : ℚ_[p]))⁻¹ • ((res G (IsoW G W la) (wl_iso_stable G W la)).E a b ^ j) y : IsoW G W la) : V) ∈ M
    rw [Submodule.coe_smul, wl_pow_coe]
    exact D.div a b hab j _ hy
  obtain ⟨hHZ, hHD⟩ := hom_divided_holds p (IsoW G W la) V (Fin n) (res G (IsoW G W la) (wl_iso_stable G W la)).E G.E
    (M.comap (IsoW G W la).subtype.toAddMonoidHom) Δ hΔZ hLd hΔD
  have hrel := hom_relation_holds ℚ_[p] (IsoW G W la) V (Fin n) (res G (IsoW G W la) (wl_iso_stable G W la)).E G.E
    (glRel_of (res G (IsoW G W la) (wl_iso_stable G W la))) (glRel_of G)
  have hφ : topC G W la ∈ HomLat (K := ℚ_[p]) (M.comap (IsoW G W la).subtype.toAddMonoidHom) Δ := by
    intro y hy
    exact subset_deltaLat p G _ ⟨wl_comp_hw G W la y.2,
      G.graded_of D.stable la _ (wl_iso_le G D.stable la y.2), D.graded la _ hy⟩
  have h2 := invariant_integral_holds p _ (Fin n) _ hrel _ hHZ hHD l (List.finRange n) (List.nodup_finRange n) _ hφ
  rw [List.length_finRange] at h2
  have h3 := h2 ⟨x, hx⟩ hxM
  rw [LinearMap.smul_apply, hid] at h3
  have h4 := hΔZ (Module.finrank ℚ_[p] (G.gS {h}) : ℚ_[p])
    (by simpa using Padic.norm_int_le_one (p := p) (Module.finrank ℚ_[p] (G.gS {h}) : ℤ)) _ h3
  rwa [smul_comm, smul_smul (Module.finrank ℚ_[p] (G.gS {h}) : ℚ_[p]), mul_inv_cancel₀ hfr, one_smul] at h4

theorem weyl_integral_holds : WeylInt := weylInt_of invariant_natural_holds (schurTrace_of invariant_inverse_holds)

end Formalism.InvariantFactorPaths.PW
