import Formalism.SharpRestriction.GlobalSchurBounds.AdmittedWeylDimension
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily

noncomputable section

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset Formalism.MainNotions.S

theorem eqvFn_finrank {G : Type} [Group G] (Γ K : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (a : Γ →* Module.End ℂ V) (ψ : K →* ℂˣ) {ι : Type} [Fintype ι] (y : ι → G)
    (hy : Function.Bijective (fun c => (Quotient.mk'' (y c) : DoubleCoset.Quotient (Γ : Set G) (K : Set G))))
    (hs : ∀ c (γ : Γ) (κ : K), (γ : G) * y c = y c * κ → γ = 1) :
    Module.finrank ℂ (eqvFn Γ K V a ψ) = Nat.card ι * Module.finrank ℂ V := by
  classical
  have dec : ∀ x : G, ∃ (c : ι) (γ : Γ) (κ : K), x = γ * y c * κ := by
    intro x
    obtain ⟨c, hc⟩ := hy.2 (Quotient.mk'' x)
    obtain ⟨h, hh, k, hk, e⟩ := (DoubleCoset.eq Γ K (y c) x).1 hc
    exact ⟨c, ⟨h, hh⟩, ⟨k, hk⟩, e⟩
  have uniq : ∀ (c c' : ι) (γ γ' : Γ) (κ κ' : K), (γ : G) * y c * κ = γ' * y c' * κ' →
      c = c' ∧ γ = γ' ∧ κ = κ' := by
    intro c c' γ γ' κ κ' e
    have hc : c = c' := by
      apply hy.1
      refine (DoubleCoset.eq Γ K (y c) (y c')).2 ⟨((γ'⁻¹ * γ : Γ) : G), (γ'⁻¹ * γ).2, ((κ * κ'⁻¹ : K) : G), (κ * κ'⁻¹).2, ?_⟩
      have : y c' = (γ' : G)⁻¹ * ((γ' : G) * y c' * κ') * (κ' : G)⁻¹ := by group
      rw [this, ← e]
      push_cast
      group
    subst hc
    have h1 : ((γ'⁻¹ * γ : Γ) : G) * y c = y c * ((κ' * κ⁻¹ : K) : G) := by
      have : (γ : G) * y c = (γ' : G) * y c * κ' * (κ : G)⁻¹ := by rw [← e]; group
      push_cast
      rw [mul_assoc, this]
      group
    have h2 := hs c _ _ h1
    have h3 : γ = γ' := by
      have := congrArg (fun z => γ' * z) h2
      simpa using this
    subst h3
    refine ⟨rfl, rfl, ?_⟩
    have := mul_left_cancel e
    exact Subtype.ext this
  choose cc gam kap hdec using dec
  let ev : eqvFn Γ K V a ψ →ₗ[ℂ] (ι → V) :=
    { toFun := fun φ c => (φ : G → V) (y c)
      map_add' := fun φ φ' => rfl
      map_smul' := fun t φ => rfl }
  have hinj : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ h0
    apply Subtype.ext
    funext x
    have h1 := φ.2 (gam x) (y (cc x)) (kap x)
    rw [← hdec x] at h1
    have h2 : (φ : G → V) (y (cc x)) = 0 := congrFun h0 (cc x)
    rw [h1, h2]
    simp
  have hsurj : Function.Surjective ev := by
    intro f
    let F : G → V := fun x => ((ψ (kap x))⁻¹ : ℂˣ) • a (gam x) (f (cc x))
    have hF : F ∈ eqvFn Γ K V a ψ := by
      intro γ x κ
      have e : ((gam (γ * x * κ) : Γ) : G) * y (cc (γ * x * κ)) * (kap (γ * x * κ) : K) =
          ((γ * gam x : Γ) : G) * y (cc x) * ((kap x * κ : K) : G) := by
        rw [← hdec (γ * x * κ)]
        conv_lhs => rw [hdec x]
        push_cast
        group
      obtain ⟨e1, e2, e3⟩ := uniq _ _ _ _ _ _ e
      show ((ψ (kap (γ * x * κ)))⁻¹ : ℂˣ) • a (gam (γ * x * κ)) (f (cc (γ * x * κ))) =
        ((ψ κ)⁻¹ : ℂˣ) • a γ (((ψ (kap x))⁻¹ : ℂˣ) • a (gam x) (f (cc x)))
      rw [e1, e2, e3, map_mul, map_mul, mul_inv, Module.End.mul_apply]
      rw [Units.smul_def, Units.smul_def, Units.smul_def, map_smul, smul_smul]
      push_cast
      rw [mul_comm]
    refine ⟨⟨F, hF⟩, ?_⟩
    funext c
    have e : ((gam (y c) : Γ) : G) * y (cc (y c)) * (kap (y c) : K) = ((1 : Γ) : G) * y c * ((1 : K) : G) := by
      rw [← hdec (y c)]; simp
    obtain ⟨e1, e2, e3⟩ := uniq _ _ _ _ _ _ e
    show ((ψ (kap (y c)))⁻¹ : ℂˣ) • a (gam (y c)) (f (cc (y c))) = f c
    rw [e1, e2, e3]
    simp
  have E := LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩
  rw [E.finrank_eq, Module.finrank_pi_fintype]
  simp [Nat.card_eq_fintype_card]

theorem stab_transfer {H : Type} [Group H] (P R U : Subgroup H) (y : P)
    (hs : R ⊓ U.map (MulAut.conj (y : H)).toMonoidHom = ⊥) (γ : R.subgroupOf P) (κ : U.subgroupOf P)
    (e : (γ : P) * y = y * κ) : γ = 1 := by
  have h1 : ((γ : P) : H) ∈ R ⊓ U.map (MulAut.conj (y : H)).toMonoidHom := by
    refine ⟨γ.2, ⟨((κ : P) : H), κ.2, ?_⟩⟩
    have e' := congrArg Subtype.val e
    simp only [Subgroup.coe_mul] at e'
    show (y : H) * ((κ : P) : H) * (y : H)⁻¹ = _
    rw [← e']
    group
  rw [hs] at h1
  exact Subtype.ext (Subtype.ext (Subgroup.mem_bot.1 h1))

theorem lemma_CL_rank_holds (D : D7) (Lv : LevelData D) : LevelDataRankBound D Lv := by
  let _ := D.host.cmStar
  intro u hs V _ _ _ a ψ
  have := (D.mem u).C.clsFin 0
  exact eqvFn_finrank (GF D) (KPi D Lv u) V a ψ (fun c => (Lv u).y c) (Lv u).y_bij
    (fun c γ κ e => stab_transfer _ _ _ ((Lv u).y c) (hs c) γ κ e)

theorem mu0Tie_of_col (D : D7) (Lv : LevelData D) (h17 : adm17 D Lv) (hp : Conclusion4p D Lv) (hg : GBig D)
    (hW : AdmittedWeylDimension D) (u : D.what₂.Word) (X : ColRep D Lv u) (hX : BaseWeightColumnCondition D Lv u X) : Mu0Tie D u :=
  mu0Tie_of_CL D Lv (lemma_CL_rank_holds D Lv) hW u (trivStab_of D Lv h17 hp hg u) X hX

end Formalism.MainNotions.StandardLattice
