import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

namespace ReadingModuleProducts

variable {G1 G2 Y1 Y2 : Type} [Group G1] [Group G2]
  {P1 : Submodule ℂ (Y1 → ℂ)} {P2 : Submodule ℂ (Y2 → ℂ)}

def prodT (A : Submodule ℂ P1) (B : Submodule ℂ P2) : A ⊗[ℂ] B →ₗ[ℂ] (Y1 × Y2 → ℂ) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun (u : A) (v : B) (x : Y1 × Y2) => u.1.1 x.1 * v.1.1 x.2)
    (fun u u' v => by funext x; simp [add_mul])
    (fun c u v => by funext x; simp [mul_assoc])
    (fun u v v' => by funext x; simp [mul_add])
    (fun c u v => by funext x; simp; ring))

@[simp] theorem prodT_tmul (A : Submodule ℂ P1) (B : Submodule ℂ P2) (u : A) (v : B) :
    prodT A B (u ⊗ₜ v) = fun x => u.1.1 x.1 * v.1.1 x.2 := rfl

theorem prodT_sum (A : Submodule ℂ P1) (B : Submodule ℂ P2) {κ : Type} (s : Finset κ) (x : κ → A) (y : κ → B) :
    prodT A B (∑ k ∈ s, x k ⊗ₜ y k) = fun z => ∑ k ∈ s, (x k).1.1 z.1 * (y k).1.1 z.2 := by
  funext z
  simp [map_sum, Finset.sum_apply]

theorem linInd {Y : Type} {P : Submodule ℂ (Y → ℂ)} {A : Submodule ℂ P} {κ : Type} (b : Module.Basis κ ℂ A) :
    LinearIndependent ℂ (fun k => (b k).1.1) :=
  b.linearIndependent.map' (P.subtype ∘ₗ A.subtype)
    (LinearMap.ker_eq_bot.2 fun _ _ h => Subtype.ext (Subtype.ext h))

theorem coeff_zero {κ : Type} (b : κ → Y2 → ℂ) (hb : LinearIndependent ℂ b) (s : Finset κ) (c : κ → Y1 → ℂ)
    (h : ∀ y1 y2, ∑ k ∈ s, c k y1 * b k y2 = 0) : ∀ k ∈ s, c k = 0 := by
  intro k hk
  funext y1
  exact linearIndependent_iff'.1 hb s (fun k => c k y1)
    (by funext y2; simpa [Finset.sum_apply] using h y1 y2) k hk

theorem expR (A : Submodule ℂ P1) (B : Submodule ℂ P2) {κ : Type} [DecidableEq κ] (b : Module.Basis κ ℂ B)
    (t : A ⊗[ℂ] B) :
    prodT A B t = fun x => ∑ k ∈ (TensorProduct.equivFinsuppOfBasisRight b t).support,
      ((TensorProduct.equivFinsuppOfBasisRight b t) k).1.1 x.1 * (b k).1.1 x.2 := by
  conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply t]
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum, prodT_sum]

theorem expL (A : Submodule ℂ P1) (B : Submodule ℂ P2) {κ : Type} [DecidableEq κ] (b : Module.Basis κ ℂ A)
    (t : A ⊗[ℂ] B) :
    prodT A B t = fun x => ∑ k ∈ (TensorProduct.equivFinsuppOfBasisLeft b t).support,
      (b k).1.1 x.1 * ((TensorProduct.equivFinsuppOfBasisLeft b t) k).1.1 x.2 := by
  conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply t]
  rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum, prodT_sum]

end ReadingModuleProducts

namespace ReadingModuleProducts

variable {G1 G2 Y1 Y2 : Type} [Group G1] [Group G2] [Monoid Y1] [Monoid Y2]
  {P1 : Submodule ℂ (Y1 → ℂ)} {P2 : Submodule ℂ (Y2 → ℂ)}

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (U : Subgroup G)
    (v : V) : v ∈ fixed ρ U ↔ ∀ u ∈ U, ρ u v = v := by
  constructor
  · intro h u hu
    simpa using h ⟨u, hu⟩
  · intro h u
    simpa using h u.1 u.2

theorem decomp (e1 : G1 →* Y1) (e2 : G2 →* Y2) (ρ1 : Representation ℂ G1 P1) (ρ2 : Representation ℂ G2 P2)
    (hρ1 : ∀ g v y, (ρ1 g v).1 y = v.1 (y * e1 g)) (hρ2 : ∀ g v y, (ρ2 g v).1 y = v.1 (y * e2 g))
    (S1 : Submodule ℂ P1) (S2 : Submodule ℂ P2) (U1 : Subgroup G1) (U2 : Subgroup G2) (t : S1 ⊗[ℂ] S2)
    (hU1 : ∀ u ∈ U1, ∀ x : Y1 × Y2, prodT S1 S2 t (x.1 * e1 u, x.2) = prodT S1 S2 t x)
    (hU2 : ∀ u ∈ U2, ∀ x : Y1 × Y2, prodT S1 S2 t (x.1, x.2 * e2 u) = prodT S1 S2 t x) :
    ∃ (κ : Type) (s : Finset κ) (x : κ → S1) (y : κ → S2), (∀ k, (x k).1 ∈ fixed ρ1 U1) ∧
      (∀ k, (y k).1 ∈ fixed ρ2 U2) ∧ LinearIndependent ℂ (fun k => (x k).1.1) ∧
      prodT S1 S2 t = fun z => ∑ k ∈ s, (x k).1.1 z.1 * (y k).1.1 z.2 := by
  classical
  set b2 := Module.Basis.ofVectorSpace ℂ S2
  set m := TensorProduct.equivFinsuppOfBasisRight b2 t
  have hx := expR S1 S2 b2 t
  have hfix : ∀ k, (m k).1 ∈ fixed ρ1 U1 := by
    intro k
    rw [mem_fixed_iff]
    intro u hu
    by_cases hk : k ∈ m.support
    · have := coeff_zero (fun k => (b2 k).1.1) (linInd b2) m.support
        (fun k y1 => (m k).1.1 (y1 * e1 u) - (m k).1.1 y1) (fun y1 y2 => by
          have h := hU1 u hu (y1, y2)
          rw [hx] at h
          simp only [sub_mul, Finset.sum_sub_distrib]
          exact sub_eq_zero.2 h) k hk
      apply Subtype.ext
      funext y
      rw [hρ1]
      exact sub_eq_zero.1 (congrFun this y)
    · rw [Finsupp.notMem_support_iff.1 hk]
      simp
  set A1 : Submodule ℂ P1 := S1 ⊓ fixed ρ1 U1
  let t' : A1 ⊗[ℂ] S2 := ∑ k ∈ m.support, (⟨(m k).1, Submodule.mem_inf.2 ⟨(m k).2, hfix k⟩⟩ : A1) ⊗ₜ b2 k
  have ht' : prodT A1 S2 t' = prodT S1 S2 t := by
    rw [hx, prodT_sum]
  set b1 := Module.Basis.ofVectorSpace ℂ A1
  set n := TensorProduct.equivFinsuppOfBasisLeft b1 t'
  have hy := expL A1 S2 b1 t'
  rw [ht'] at hy
  refine ⟨_, n.support, fun l => ⟨(b1 l).1, (Submodule.mem_inf.1 (b1 l).2).1⟩, n, fun l => (Submodule.mem_inf.1 (b1 l).2).2,
    ?_, linInd b1, hy⟩
  intro l
  rw [mem_fixed_iff]
  intro u hu
  by_cases hl : l ∈ n.support
  · have := coeff_zero (fun l => (b1 l).1.1) (linInd b1) n.support
      (fun l y2 => (n l).1.1 (y2 * e2 u) - (n l).1.1 y2) (fun y2 y1 => by
        have h := hU2 u hu (y1, y2)
        rw [hy] at h
        simp only [sub_mul, Finset.sum_sub_distrib]
        refine sub_eq_zero.2 ?_
        simpa only [mul_comm] using h) l hl
    apply Subtype.ext
    funext y
    rw [hρ2]
    exact sub_eq_zero.1 (congrFun this y)
  · rw [Finsupp.notMem_support_iff.1 hl]
    simp

end ReadingModuleProducts

namespace ReadingModuleProducts

variable {G1 G2 Y1 Y2 : Type} [Group G1] [Group G2] [Monoid Y1] [Monoid Y2]
  {P1 : Submodule ℂ (Y1 → ℂ)} {P2 : Submodule ℂ (Y2 → ℂ)}

theorem sep_pair [TopologicalSpace G1] [TopologicalSpace G2] {X1 X2 : Type} [AddCommGroup X1] [Module ℂ X1]
    [AddCommGroup X2] [Module ℂ X2] (e1 : G1 →* Y1) (e2 : G2 →* Y2) (ρ1 : Representation ℂ G1 P1)
    (ρ2 : Representation ℂ G2 P2) (hρ1 : ∀ g v y, (ρ1 g v).1 y = v.1 (y * e1 g))
    (hρ2 : ∀ g v y, (ρ2 g v).1 y = v.1 (y * e2 g)) (ρ : Representation ℂ (G1 × G2) (Y1 × Y2 → ℂ))
    (hρ : ∀ g F x, ρ g F x = F (x.1 * e1 g.1, x.2 * e2 g.2)) (S1 : Submodule ℂ P1) (S2 : Submodule ℂ P2)
    (τ1 : Representation ℂ G1 X1) (τ2 : Representation ℂ G2 X2) (h1 : Sep ρ1 S1 τ1) (h2 : Sep ρ2 S2 τ2) :
    Sep ρ (Submodule.span ℂ {F | ∃ φ₁ ∈ S1, ∃ φ₂ ∈ S2, F = fun x => φ₁.1 x.1 * φ₂.1 x.2})
      (GlobalTheory.SmGL.extTensor τ1 τ2) := by
  classical
  obtain ⟨hs1, J1, L1, heq1, hsep1⟩ := h1
  obtain ⟨hs2, J2, L2, heq2, hsep2⟩ := h2
  have hR : Submodule.span ℂ {F | ∃ φ₁ ∈ S1, ∃ φ₂ ∈ S2, F = fun x => φ₁.1 x.1 * φ₂.1 x.2} =
      LinearMap.range (prodT S1 S2) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro F ⟨φ₁, h₁, φ₂, h₂, rfl⟩
      exact ⟨(⟨φ₁, h₁⟩ : S1) ⊗ₜ (⟨φ₂, h₂⟩ : S2), rfl⟩
    · rintro F ⟨t, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul u v => exact Submodule.subset_span ⟨u.1, u.2, v.1, v.2, rfl⟩
      | add t t' ht ht' => rw [map_add]; exact add_mem ht ht'
  rw [hR]
  set Ψ := prodT S1 S2
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro t ht
    rw [LinearMap.mem_ker] at ht
    set b2 := Module.Basis.ofVectorSpace ℂ S2
    set m := TensorProduct.equivFinsuppOfBasisRight b2 t
    have hx := expR S1 S2 b2 t
    rw [ht] at hx
    have hz := coeff_zero (fun k => (b2 k).1.1) (linInd b2) m.support (fun k => (m k).1.1)
      (fun y1 y2 => (congrFun hx (y1, y2)).symm)
    have hm : m = 0 := by
      ext k : 1
      by_cases hk : k ∈ m.support
      · exact Subtype.ext (Subtype.ext (hz k hk))
      · exact Finsupp.notMem_support_iff.1 hk
    have : t = (TensorProduct.equivFinsuppOfBasisRight b2).symm m := by simp [m]
    rw [this, hm, map_zero]
  set e := LinearEquiv.ofInjective Ψ hinj
  have hL : ∀ j : J1 × J2, ∃ g : (Y1 × Y2 → ℂ) →ₗ[ℂ] X1 ⊗[ℂ] X2, g ∘ₗ (LinearMap.range Ψ).subtype =
      (TensorProduct.map (L1 j.1 ∘ₗ S1.subtype) (L2 j.2 ∘ₗ S2.subtype)) ∘ₗ e.symm.toLinearMap :=
    fun j => LinearMap.exists_extend _
  choose L hLs using hL
  have spec : ∀ j t, L j (Ψ t) = TensorProduct.map (L1 j.1 ∘ₗ S1.subtype) (L2 j.2 ∘ₗ S2.subtype) t := by
    intro j t
    have h := LinearMap.congr_fun (hLs j) (e t)
    simpa [e] using h
  have specS : ∀ j {κ : Type} (s : Finset κ) (x : κ → S1) (y : κ → S2),
      L j (fun z => ∑ k ∈ s, (x k).1.1 z.1 * (y k).1.1 z.2) = ∑ k ∈ s, L1 j.1 (x k).1 ⊗ₜ L2 j.2 (y k).1 := by
    intro j κ s x y
    rw [← prodT_sum, spec]
    simp [map_sum]

  have hdec : ∀ G ∈ LinearMap.range Ψ, SmVec ρ G → ∃ (U1 : Subgroup G1) (U2 : Subgroup G2) (κ : Type) (s : Finset κ)
      (x : κ → S1) (y : κ → S2), IsOpen (U1 : Set G1) ∧ IsOpen (U2 : Set G2) ∧ (∀ k, (x k).1 ∈ fixed ρ1 U1) ∧
      (∀ k, (y k).1 ∈ fixed ρ2 U2) ∧ LinearIndependent ℂ (fun k => (x k).1.1) ∧
      G = fun z => ∑ k ∈ s, (x k).1.1 z.1 * (y k).1.1 z.2 := by
    rintro G ⟨t, rfl⟩ ⟨U, hUo, hU⟩
    rw [mem_fixed_iff] at hU
    obtain ⟨κ, s, x, y, hx, hy, hli, hG⟩ := decomp e1 e2 ρ1 ρ2 hρ1 hρ2 S1 S2 (U.comap (MonoidHom.inl G1 G2))
      (U.comap (MonoidHom.inr G1 G2)) t
      (fun u hu z => by simpa [hρ] using congrFun (hU (u, 1) hu) z)
      (fun u hu z => by simpa [hρ] using congrFun (hU (1, u) hu) z)
    exact ⟨_, _, κ, s, x, y, hUo.preimage (continuous_id.prodMk continuous_const),
      hUo.preimage (continuous_const.prodMk continuous_id), hx, hy, hli, hG⟩
  refine ⟨?_, J1 × J2, L, ?_, ?_⟩
  · intro g G hG
    obtain ⟨t, rfl⟩ := hG
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul u v =>
      refine ⟨(⟨ρ1 g.1 u.1, hs1 g.1 u.1 u.2⟩ : S1) ⊗ₜ (⟨ρ2 g.2 v.1, hs2 g.2 v.1 v.2⟩ : S2), ?_⟩
      funext z
      simp [Ψ, hρ, hρ1, hρ2]
    | add t t' ht ht' => rw [map_add, map_add]; exact add_mem ht ht'
  · intro j g G hG hsm
    obtain ⟨U1, U2, κ, s, x, y, hU1o, hU2o, hx, hy, -, rfl⟩ := hdec G hG hsm
    have hG' : ρ g (fun z => ∑ k ∈ s, (x k).1.1 z.1 * (y k).1.1 z.2) =
        fun z => ∑ k ∈ s, ((⟨ρ1 g.1 (x k).1, hs1 g.1 _ (x k).2⟩ : S1)).1.1 z.1 *
          ((⟨ρ2 g.2 (y k).1, hs2 g.2 _ (y k).2⟩ : S2)).1.1 z.2 := by
      funext z
      simp [hρ, hρ1, hρ2]
    rw [hG', specS, specS, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [heq1 j.1 g.1 _ (x k).2 ⟨U1, hU1o, hx k⟩, heq2 j.2 g.2 _ (y k).2 ⟨U2, hU2o, hy k⟩, GlobalTheory.SmGL.extTensor_tmul]
  · intro G hG hsm h0
    obtain ⟨U1, U2, κ, s, x, y, hU1o, hU2o, hx, hy, hli, rfl⟩ := hdec G hG hsm
    have hy0 : ∀ k ∈ s, y k = 0 := by
      intro k hk
      apply Subtype.ext
      refine hsep2 _ (y k).2 ⟨U2, hU2o, hy k⟩ fun j2 => ?_
      rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
      intro β
      set c : κ → ℂ := fun k => β (L2 j2 (y k).1) with hc
      have hw : ∑ k ∈ s, c k • (x k).1 = 0 := by
        refine hsep1 _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (x k).2)
          ⟨U1, hU1o, Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hx k)⟩ fun j1 => ?_
        have h := congrArg (fun u => TensorProduct.rid ℂ X1 (LinearMap.lTensor X1 β u)) (h0 (j1, j2))
        simp only [specS, map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, map_zero] at h
        simpa [map_sum, hc] using h
      exact linearIndependent_iff'.1 hli s c (by
        have := congrArg (fun v : P1 => v.1) hw
        simpa using this) k hk
    funext z
    simp only [Pi.zero_apply]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [hy0 k hk]
    simp

end ReadingModuleProducts

theorem readModOf_holds : ReadModOf := by
  intro hT E _ _ _ a b s₁ s₂ Pa Pb w g₁ g₂ u₁ u₂ t₁ t₂
  exact ReadingModuleProducts.sep_pair (embW a w) (embW b w) ((finRep E a).comp (locGL E a w))
    ((finRep E b).comp (locGL E b w)) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (pairRt a b w) (fun _ _ _ => rfl)
    s₁.space s₂.space _ _ (hT E a s₁ Pa w g₁ u₁ t₁) (hT E b s₂ Pb w g₂ u₂ t₂)

end PositivityTheory.Rg.BcB.F.RS

end
