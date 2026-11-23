import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTKLineCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IrreducibleCapelliModules

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLIso

noncomputable section

section Cyc

variable {U : Type} [AddCommGroup U] [Module ℂ U] {n : ℕ}

def S (E : Fin n → Fin n → Module.End ℂ U) (x0 : U) : ℕ → Submodule ℂ U
  | 0 => ℂ ∙ x0
  | j + 1 => S E x0 j ⊔ ⨆ c, ⨆ d, (S E x0 j).map (E c d)

theorem S_le_succ (E : Fin n → Fin n → Module.End ℂ U) (x0 : U) (j : ℕ) : S E x0 j ≤ S E x0 (j + 1) :=
  le_sup_left

theorem E_mem_S (E : Fin n → Fin n → Module.End ℂ U) (x0 : U) {j : ℕ} {y : U} (hy : y ∈ S E x0 j) (c d : Fin n) :
    E c d y ∈ S E x0 (j + 1) := by
  have h : (S E x0 j).map (E c d) ≤ S E x0 (j + 1) :=
    le_sup_of_le_right (le_iSup_of_le c (le_iSup_of_le d le_rfl))
  exact h (Submodule.mem_map_of_mem hy)

theorem base_vector_mem_span_filtration (E : Fin n → Fin n → Module.End ℂ U) (x0 : U) : ∀ j, x0 ∈ S E x0 j
  | 0 => Submodule.mem_span_singleton_self x0
  | j + 1 => S_le_succ E x0 j (base_vector_mem_span_filtration E x0 j)

theorem S_mono (E : Fin n → Fin n → Module.End ℂ U) (x0 : U) : Monotone (S E x0) :=
  monotone_nat_of_le_succ (S_le_succ E x0)

theorem raise_S {E : Fin n → Fin n → Module.End ℂ U} {x0 : U} (hgl : GlRel E) (hx : ∀ a b, a < b → E a b x0 = 0) :
    ∀ j, ∀ a b : Fin n, a < b → ∀ y ∈ S E x0 j, E a b y ∈ S E x0 j := by
  intro j
  induction j with
  | zero =>
    intro a b hab y hy
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_smul, hx a b hab, smul_zero]
    exact Submodule.zero_mem _
  | succ j ih =>
    intro a b hab y hy
    have hle : S E x0 (j + 1) ≤ (S E x0 (j + 1)).comap (E a b) := by
      apply sup_le
      · intro u hu
        exact S_le_succ E x0 j (ih a b hab u hu)
      · refine iSup_le fun c => iSup_le fun d => ?_
        rw [Submodule.map_le_iff_le_comap]
        intro u hu
        show E a b (E c d u) ∈ S E x0 (j + 1)
        have hc := congrArg (fun T : Module.End ℂ U => T u) (hgl a b c d)
        simp only [LinearMap.sub_apply, Module.End.mul_apply] at hc
        have hsplit : E a b (E c d u) = E c d (E a b u) +
            ((if b = c then E a d else 0) - (if d = a then E c b else 0)) u := by
          rw [LinearMap.sub_apply, ← hc]; abel
        rw [hsplit, LinearMap.sub_apply]
        refine Submodule.add_mem _ (E_mem_S E x0 (ih a b hab u hu) c d) (Submodule.sub_mem _ ?_ ?_)
        · split_ifs
          · exact E_mem_S E x0 hu a d
          · rw [LinearMap.zero_apply]; exact Submodule.zero_mem _
        · split_ifs
          · exact E_mem_S E x0 hu c b
          · rw [LinearMap.zero_apply]; exact Submodule.zero_mem _
    exact hle hy

theorem psi_S {E : Fin n → Fin n → Module.End ℂ U} {x0 : U} {ν : Fin n → ℂ} (hgl : GlRel E) (hx : IsHW E ν x0)
    (ψ : U →ₗ[ℂ] ℂ) (hlow : ∀ a b : Fin n, b < a → ∀ u, ψ (E a b u) = 0)
    (hdiag : ∀ (a : Fin n) (u : U), ψ (E a a u) = ν a * ψ u) (h0 : ψ x0 = 0) :
    ∀ j, ∀ y ∈ S E x0 j, ψ y = 0 := by
  intro j
  induction j with
  | zero =>
    intro y hy
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_smul, h0, smul_zero]
  | succ j ih =>
    have hle : S E x0 (j + 1) ≤ LinearMap.ker ψ := by
      apply sup_le
      · intro u hu; exact ih u hu
      · refine iSup_le fun c => iSup_le fun d => ?_
        rw [Submodule.map_le_iff_le_comap]
        intro u hu
        show ψ (E c d u) = 0
        rcases lt_trichotomy c d with h | h | h
        · exact ih _ (raise_S hgl hx.2 j c d h u hu)
        · subst h; rw [hdiag, ih u hu, mul_zero]
        · exact hlow c d h u
    intro y hy
    exact hle hy

def W (E : Fin n → Fin n → Module.End ℂ U) (x0 : U) : Submodule ℂ U := ⨆ j, S E x0 j

theorem mem_W {E : Fin n → Fin n → Module.End ℂ U} {x0 y : U} : y ∈ W E x0 ↔ ∃ j, y ∈ S E x0 j :=
  Submodule.mem_iSup_of_directed _ (S_mono E x0).directed_le

theorem base_point_mem_half_plane_alt (E : Fin n → Fin n → Module.End ℂ U) (x0 : U) : x0 ∈ W E x0 :=
  mem_W.mpr ⟨0, base_vector_mem_span_filtration E x0 0⟩

theorem W_stab (E : Fin n → Fin n → Module.End ℂ U) (x0 : U) : Qr.Stab E (W E x0) := by
  intro a b y hy
  obtain ⟨j, hj⟩ := mem_W.mp hy
  exact mem_W.mpr ⟨j + 1, E_mem_S E x0 hj a b⟩

theorem lowest_functional_vanishes_on_module {E : Fin n → Fin n → Module.End ℂ U} {x0 : U} {ν : Fin n → ℂ} (hgl : GlRel E) (hx : IsHW E ν x0)
    (ψ : U →ₗ[ℂ] ℂ) (hlow : ∀ a b : Fin n, b < a → ∀ u, ψ (E a b u) = 0)
    (hdiag : ∀ (a : Fin n) (u : U), ψ (E a a u) = ν a * ψ u) (h0 : ψ x0 = 0) : ∀ y ∈ W E x0, ψ y = 0 := by
  intro y hy
  obtain ⟨j, hj⟩ := mem_W.mp hy
  exact psi_S hgl hx ψ hlow hdiag h0 j y hj

end Cyc

section HW

theorem hw_of {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (m : Fin n → ℂ) (hgl : GlRel E) (hsd : Qr.SDec m)
    (hcap : ∀ (w : ℂ) (v : V), qdet E w v = Qr.cpol m w • v) :
    ∃ v : V, v ≠ 0 ∧ IsHW E (fun j => m j + ((j : ℕ) : ℂ)) v := by
  have htop : Qr.CapSp E m = ⊤ := eq_top_iff.mpr fun x _ => Qr.mem_CapSp.mpr fun w => hcap w x
  obtain ⟨ν, v, -, hv0, hhw, -⟩ :=
    exists_singular_maximal_vector V n E hgl ⊤ (fun _ _ _ _ => trivial) top_ne_bot
  have hs := (capelli_singular V n E m hgl (by rw [htop]; exact top_ne_bot)).2 hsd ν v
    (by rw [htop]; trivial) hv0 hhw
  have hν : ν = fun j => m j + ((j : ℕ) : ℂ) := funext hs
  exact ⟨v, hv0, hν ▸ hhw⟩

theorem functional_of {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (m : Fin n → ℂ) (hgl : GlRel E) (hirr : Qr.Irr E) (hsd : Qr.SDec m)
    (hcap : ∀ (w : ℂ) (v : V), qdet E w v = Qr.cpol m w • v) (v : V) (hv : IsHW E (fun j => m j + ((j : ℕ) : ℂ)) v)
    (hv0 : v ≠ 0) :
    ∃ φ : V →ₗ[ℂ] ℂ, φ v = 1 ∧ (∀ a b : Fin n, b < a → ∀ u, φ (E a b u) = 0) ∧
      ∀ (a : Fin n) (u : V), φ (E a a u) = (m a + ((a : ℕ) : ℂ)) * φ u := by
  classical
  obtain ⟨hdgl, hdmin⟩ := dual_minor V n E hgl
  have : Nontrivial (Module.Dual ℂ V) := by
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ V, f v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv0 ((Module.forall_dual_apply_eq_zero_iff ℂ v).mp hcon)
    exact ⟨⟨f, 0, fun h => hf (by rw [h]; rfl)⟩⟩
  have hdcap : ∀ (w : ℂ) (f : Module.Dual ℂ V), qdet (Qr.dualE E) w f = Qr.cpol m w • f := by
    intro w f
    have h := hdmin n id id w
    show qminor (Qr.dualE E) id id w f = _
    rw [h]
    ext x
    simp only [LinearMap.dualMap_apply, LinearMap.smul_apply, smul_eq_mul]
    have := hcap w x
    unfold qdet at this
    rw [this, map_smul, smul_eq_mul]
  obtain ⟨φ0, hφ0, hφhw⟩ := hw_of (Qr.dualE E) m hdgl hsd hdcap
  have hlow0 : ∀ a b : Fin n, b < a → ∀ u, φ0 (E a b u) = 0 := by
    intro a b hba u
    have h := congrArg (fun f : Module.Dual ℂ V => f u) (hφhw.2 b a hba)
    simpa [Qr.dualE, LinearMap.dualMap_apply] using h
  have hdiag0 : ∀ (a : Fin n) (u : V), φ0 (E a a u) = (m a + ((a : ℕ) : ℂ)) * φ0 u := by
    intro a u
    have h := congrArg (fun f : Module.Dual ℂ V => f u) (hφhw.1 a)
    simpa [Qr.dualE, LinearMap.dualMap_apply] using h
  have hne : φ0 v ≠ 0 := by
    intro h0
    apply hφ0
    have hW : W E v = ⊤ := by
      rcases hirr.2 (W E v) (W_stab E v) with h | h
      · exfalso; apply hv0
        have := base_point_mem_half_plane_alt E v
        rw [h] at this
        exact (Submodule.mem_bot ℂ).mp this
      · exact h
    ext x
    have := lowest_functional_vanishes_on_module hgl hv φ0 hlow0 hdiag0 h0 x (by rw [hW]; trivial)
    simpa using this
  refine ⟨(φ0 v)⁻¹ • φ0, ?_, ?_, ?_⟩
  · simp [hne]
  · intro a b hba u
    simp [hlow0 a b hba u]
  · intro a u
    simp only [LinearMap.smul_apply, smul_eq_mul, hdiag0 a u]
    ring

end HW

section Prod

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n : ℕ}

def Ep (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ V') :
    Fin n → Fin n → Module.End ℂ (V × V') :=
  fun a b => LinearMap.prodMap (E a b) (E' a b)

theorem glRel_Ep {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'} (hgl : GlRel E)
    (hgl' : GlRel E') : GlRel (Ep E E') := by
  intro a b c d
  apply LinearMap.ext
  intro p
  have h1 := congrArg (fun T : Module.End ℂ V => T p.1) (hgl a b c d)
  have h2 := congrArg (fun T : Module.End ℂ V' => T p.2) (hgl' a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1 h2
  apply Prod.ext
  · simp only [Ep, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.prodMap_apply, Prod.fst_sub]
    rw [h1]
    split_ifs <;> simp
  · simp only [Ep, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.prodMap_apply, Prod.snd_sub]
    rw [h2]
    split_ifs <;> simp

end Prod

theorem lie_algebra_isomorphism_holds : KLIsoAlg := by
  intro V V' _ _ _ _ _ _ n E E' m hgl hgl' hirr hirr' hsd hcap hcap'
  classical
  have := hirr.1
  have := hirr'.1
  obtain ⟨v, hv0, hvhw⟩ := hw_of E m hgl hsd hcap
  obtain ⟨v', hv0', hvhw'⟩ := hw_of E' m hgl' hsd hcap'
  obtain ⟨φ, hφv, hφlow, hφdiag⟩ := functional_of E m hgl hirr hsd hcap v hvhw hv0
  obtain ⟨φ', hφv', hφlow', hφdiag'⟩ := functional_of E' m hgl' hirr' hsd hcap' v' hvhw' hv0'
  set ν : Fin n → ℂ := fun j => m j + ((j : ℕ) : ℂ) with hν
  set F := Ep E E' with hF
  have hglF : GlRel F := glRel_Ep hgl hgl'
  set x0 : V × V' := (v, v') with hx0
  have hx : IsHW F ν x0 := by
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · simp only [hF, Ep, hx0, LinearMap.prodMap_apply, hvhw.1 a, hvhw'.1 a, Prod.smul_mk]
    · simp only [hF, Ep, hx0, LinearMap.prodMap_apply, hvhw.2 a b hab, hvhw'.2 a b hab, Prod.mk_zero_zero]
  set ψ : V × V' →ₗ[ℂ] ℂ := φ.comp (LinearMap.fst ℂ V V') - φ'.comp (LinearMap.snd ℂ V V') with hψ
  have hψlow : ∀ a b : Fin n, b < a → ∀ u, ψ (F a b u) = 0 := by
    intro a b hba u
    simp [hψ, hF, Ep, hφlow a b hba, hφlow' a b hba]
  have hψdiag : ∀ (a : Fin n) (u : V × V'), ψ (F a a u) = ν a * ψ u := by
    intro a u
    simp only [hψ, hF, Ep, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      LinearMap.prodMap_apply, hφdiag, hφdiag', hν]
    ring
  have hψ0 : ψ x0 = 0 := by simp [hψ, hx0, hφv, hφv']
  have hkill := lowest_functional_vanishes_on_module hglF hx ψ hψlow hψdiag hψ0
  set Wm := W F x0 with hWm
  have hstab := W_stab F x0

  set K : Submodule ℂ V := Wm.comap (LinearMap.inl ℂ V V') with hK
  have hKst : Qr.Stab E K := by
    intro a b x hx'
    show (E a b x, (0 : V')) ∈ Wm
    have := hstab a b (x, 0) hx'
    simpa [hF, Ep] using this
  have hKbot : K = ⊥ := by
    rcases hirr.2 K hKst with h | h
    · exact h
    · exfalso
      have hvK : v ∈ K := by rw [h]; trivial
      have := hkill (v, 0) hvK
      simp [hψ, hφv] at this
  set p2 : Wm →ₗ[ℂ] V' := (LinearMap.snd ℂ V V').comp Wm.subtype with hp2
  have hinj : Function.Injective p2 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h2 : (w : V × V').2 = 0 := hw
    have hmem : (w : V × V').1 ∈ K := by
      show ((w : V × V').1, (0 : V')) ∈ Wm
      have : ((w : V × V').1, (0 : V')) = (w : V × V') := by ext <;> simp [h2]
      rw [this]; exact w.2
    rw [hKbot] at hmem
    have h1 : (w : V × V').1 = 0 := (Submodule.mem_bot ℂ).mp hmem
    ext <;> simp [h1, h2]
  have hsurj : Function.Surjective p2 := by
    rw [← LinearMap.range_eq_top]
    have hRst : Qr.Stab E' (LinearMap.range p2) := by
      intro a b y hy
      obtain ⟨w, rfl⟩ := hy
      refine ⟨⟨F a b (w : V × V'), hstab a b _ w.2⟩, ?_⟩
      simp [hp2, hF, Ep]
    rcases hirr'.2 _ hRst with h | h
    · exfalso; apply hv0'
      have : v' ∈ LinearMap.range p2 := ⟨⟨x0, base_point_mem_half_plane_alt F x0⟩, by simp [hp2, hx0]⟩
      rw [h] at this
      exact (Submodule.mem_bot ℂ).mp this
    · exact h
  set eqv := LinearEquiv.ofBijective p2 ⟨hinj, hsurj⟩ with heqv
  set A : V' →ₗ[ℂ] V := (LinearMap.fst ℂ V V').comp (Wm.subtype.comp eqv.symm.toLinearMap) with hA
  have hAv : A v' = v := by
    have hs : eqv.symm v' = ⟨x0, base_point_mem_half_plane_alt F x0⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      simp [heqv, hp2, hx0]
    simp [hA, hs, hx0]
  refine ⟨A, fun h0 => hv0 ?_, fun a b => ?_⟩
  · rw [← hAv, h0, LinearMap.zero_apply]
  · apply LinearMap.ext
    intro y
    set w := eqv.symm y with hw
    have hpw : p2 w = y := by rw [hw]; exact eqv.apply_symm_apply y
    have hs : eqv.symm (E' a b y) = ⟨F a b (w : V × V'), hstab a b _ w.2⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      show E' a b y = p2 ⟨F a b (w : V × V'), hstab a b _ w.2⟩
      rw [← hpw]
      simp [hp2, hF, Ep]
    simp only [LinearMap.comp_apply, hA, LinearEquiv.coe_coe, hs, Submodule.subtype_apply, LinearMap.fst_apply,
      hF, Ep, LinearMap.prodMap_apply, hw]

example : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLIsoAlg := lie_algebra_isomorphism_holds

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLIso
