import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DefFree

theorem exists_adForms_value {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (hχ : ∀ k, χ k = 1) (x₀ : G)
    (hfree : ∀ γ : Γ, ∀ k ∈ J, ι γ * x₀ = x₀ * k → γ = 1) (w : W) :
    ∃ f ∈ Formalism.IndefR.Bridge.AdForms ι ρ J χ, f x₀ = w ∧
      ∀ y, (¬ ∃ γ : Γ, ∃ k ∈ J, y = ι γ * x₀ * k) → f y = 0 := by
  classical

  have huniq : ∀ (γ γ' : Γ) (k k' : G), k ∈ J → k' ∈ J → ι γ * x₀ * k = ι γ' * x₀ * k' → γ = γ' := by
    intro γ γ' k k' hk hk' e
    have e' : ι (γ'⁻¹ * γ) * x₀ = x₀ * (k' * k⁻¹) := by
      calc ι (γ'⁻¹ * γ) * x₀ = (ι γ')⁻¹ * (ι γ * x₀ * k) * k⁻¹ := by rw [map_mul, map_inv]; group
        _ = (ι γ')⁻¹ * (ι γ' * x₀ * k') * k⁻¹ := by rw [e]
        _ = x₀ * (k' * k⁻¹) := by group
    exact (inv_mul_eq_one.mp (hfree _ _ (J.mul_mem hk' (J.inv_mem hk)) e')).symm
  have hval : ∀ (y : G) (hy : ∃ γ : Γ, ∃ k ∈ J, y = ι γ * x₀ * k) (γ : Γ) (k : G), k ∈ J → y = ι γ * x₀ * k →
      hy.choose = γ := by
    intro y hy γ k hk e
    obtain ⟨k₀, hk₀, e₀⟩ := hy.choose_spec
    exact huniq _ _ _ _ hk₀ hk (e₀.symm.trans e)
  refine ⟨fun y => if hy : ∃ γ : Γ, ∃ k ∈ J, y = ι γ * x₀ * k then ρ hy.choose w else 0, ?_, ?_, ?_⟩
  · show ∀ (γ : Γ) (h : G) (k : J), _ = _
    intro γ h k
    simp only [hχ, Units.val_one, one_smul]
    by_cases hh : ∃ γ₁ : Γ, ∃ k₁ ∈ J, h = ι γ₁ * x₀ * k₁
    · obtain ⟨γ₁, k₁, hk₁, rfl⟩ := hh
      have e2 : ι γ * (ι γ₁ * x₀ * k₁) * (k : G) = ι (γ * γ₁) * x₀ * (k₁ * k) := by
        rw [map_mul]; group
      have h2 : ∃ γ' : Γ, ∃ k' ∈ J, ι γ * (ι γ₁ * x₀ * k₁) * (k : G) = ι γ' * x₀ * k' :=
        ⟨γ * γ₁, k₁ * k, J.mul_mem hk₁ k.2, e2⟩
      have h1 : ∃ γ' : Γ, ∃ k' ∈ J, ι γ₁ * x₀ * k₁ = ι γ' * x₀ * k' := ⟨γ₁, k₁, hk₁, rfl⟩
      rw [dif_pos h2, dif_pos h1, hval _ h2 (γ * γ₁) (k₁ * k) (J.mul_mem hk₁ k.2) e2,
        hval _ h1 γ₁ k₁ hk₁ rfl, map_mul, Module.End.mul_apply]
    · have h2 : ¬ ∃ γ' : Γ, ∃ k' ∈ J, ι γ * h * (k : G) = ι γ' * x₀ * k' := by
        rintro ⟨γ', k', hk', e⟩
        refine hh ⟨γ⁻¹ * γ', k' * (k : G)⁻¹, J.mul_mem hk' (J.inv_mem k.2), ?_⟩
        calc h = (ι γ)⁻¹ * (ι γ * h * (k : G)) * (k : G)⁻¹ := by group
          _ = ι (γ⁻¹ * γ') * x₀ * (k' * (k : G)⁻¹) := by rw [e, map_mul, map_inv]; group
      rw [dif_neg h2, dif_neg hh, map_zero]
  · have h0 : ∃ γ : Γ, ∃ k ∈ J, x₀ = ι γ * x₀ * k := ⟨1, 1, J.one_mem, by simp⟩
    dsimp only
    rw [dif_pos h0, hval _ h0 1 1 J.one_mem (by simp), map_one, Module.End.one_apply]
  · intro y hy
    dsimp only
    rw [dif_neg hy]

theorem eq_one_of_gam_bot {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {n : ℕ} {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {K : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))}
    (hG : ∀ c₀ : Cl hc J K, Gam c₀ = ⊥) (x u : UA hc J) (hu : u ∈ UQ hc J)
    (hk : ((x⁻¹ * u * x : UA hc J) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ K) : u = 1 := by
  rw [Subgroup.mem_subgroupOf] at hu
  simp only [Formalism.UG.ratPts, Subgroup.mem_map] at hu
  obtain ⟨g, hg, hgu⟩ := hu
  obtain ⟨q, hq, k₁, hk₁, e3⟩ := (DoubleCoset.eq (UQ hc J) (K.subgroupOf (UA hc J))
    (Formalism.L2.DIV.rep (Quotient.mk'' x : Cl hc J K)) x).1 (Formalism.L2.DIV.mk_rep _)
  rw [Subgroup.mem_subgroupOf] at hq hk₁
  simp only [Formalism.UG.ratPts, Subgroup.mem_map] at hq
  obtain ⟨gq, hgq, hgqe⟩ := hq
  have hmem : gq⁻¹ * g * gq ∈ Formalism.L2.DIV.UR hc J :=
    (Formalism.L2.DIV.UR hc J).mul_mem ((Formalism.L2.DIV.UR hc J).mul_mem ((Formalism.L2.DIV.UR hc J).inv_mem hgq) hg) hgq
  have hx : ((x : UA hc J) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      (q : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * (Formalism.L2.DIV.rep (Quotient.mk'' x : Cl hc J K) : UA hc J) * k₁ := by
    have h3 := congrArg Subtype.val e3
    simpa only [Subgroup.coe_mul] using h3
  have hk0 : (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * u * x ∈ K := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hk
  have hin : (⟨gq⁻¹ * g * gq, hmem⟩ : Formalism.L2.DIV.UR hc J) ∈ Formalism.L2.DIV.Gam (Quotient.mk'' x : Cl hc J K) := by
    show Formalism.L2.DIV.conjIn hc J _ _ ∈ K
    rw [Formalism.L2.DIV.conjIn_apply]
    have hr : ((Formalism.L2.DIV.rep (Quotient.mk'' x : Cl hc J K) : UA hc J) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        (q : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * x * (k₁ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ := by
      rw [hx]; group
    simp only [map_mul, map_inv, hgu, hgqe]
    rw [hr]
    have e4 : ((q : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * x * (k₁ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹)⁻¹ *
        ((q : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * u * q) *
        ((q : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * x * (k₁ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹) =
        (k₁ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * ((x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * u * x) *
          (k₁ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ := by group
    rw [e4]
    exact K.mul_mem (K.mul_mem hk₁ hk0) (K.inv_mem hk₁)
  have hb : (⟨gq⁻¹ * g * gq, hmem⟩ : Formalism.L2.DIV.UR hc J) ∈ (⊥ : Subgroup (Formalism.L2.DIV.UR hc J)) := by
    rw [← hG (Quotient.mk'' x)]
    exact hin
  have h1 : gq⁻¹ * g * gq = 1 := congrArg Subtype.val (Subgroup.mem_bot.1 hb)
  have hg1 : g = 1 := by
    calc g = gq * (gq⁻¹ * g * gq) * gq⁻¹ := by group
      _ = 1 := by rw [h1]; group
  apply Subtype.ext
  rw [← hgu, hg1, map_one]
  rfl

section

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem finE_of_eq {γ : GQ V} {h h' κ : GA D V} {k : Formalism.IndefR.Bridge.Gf V} (hk : finHom V κ = k.1)
    (e : (finHom V).rangeRestrict h' = Formalism.IndefR.Bridge.ratF V γ * (finHom V).rangeRestrict h * k) :
    finU V h' = finU V γ * finU V h * finU V κ := by
  apply Subtype.ext
  have e' := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, MonoidHom.coe_rangeRestrict, Formalism.IndefR.Bridge.ratF, MonoidHom.comp_apply,
    Subgroup.coe_subtype] at e'
  simp only [Subgroup.coe_mul, coe_finU, finE_eq, e', hk, map_mul]

theorem finE_mem_lev {κ : GA D V} {k : Formalism.IndefR.Bridge.Gf V} (hk : finHom V κ = k.1) (h : k ∈ (levEnv V β L).J) :
    finE V κ ∈ lev D.sp.cm V.gram β (flag1L L) := by
  rw [finE_eq, hk]
  exact h

theorem stab_trivial (hG : ∀ c₀ : Cl D.sp.cm V.gram (lev D.sp.cm V.gram β (flag1L L)), Gam c₀ = ⊥) (h : GA D V)
    (γ : GQ V) (k : Formalism.IndefR.Bridge.Gf V) (hk : k ∈ (levEnv V β L).J)
    (e : Formalism.IndefR.Bridge.ratF V γ * (finHom V).rangeRestrict h = (finHom V).rangeRestrict h * k) : γ = 1 := by
  obtain ⟨κ, hκ⟩ := MonoidHom.mem_range.1 k.2
  have e' := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, MonoidHom.coe_rangeRestrict, Formalism.IndefR.Bridge.ratF, MonoidHom.comp_apply,
    Subgroup.coe_subtype] at e'
  have hk' : (k : GL (Fin V.rank) _) = (finHom V h)⁻¹ * finHom V γ * finHom V h := by
    rw [mul_assoc, e']; group
  have key : (((finU V h)⁻¹ * finU V γ * finU V h : UA D.sp.cm V.gram) : GL (Fin V.rank) (EAf D)) = finE V κ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_finU, finE_eq, hκ, hk', map_mul, map_inv]
  have hu := eq_one_of_gam_bot hG (finU V h) (finU V γ) (AdelCls.rat_mem V γ γ.2)
    (by rw [key]; exact finE_mem_lev hκ hk)
  exact Subtype.ext (AdelCls.rat_inj V γ γ.2 hu)

set_option maxHeartbeats 1000000 in
private theorem clsA_eq_of_ratF_mul {h h' : GA D V} {γ : GQ V} {k : Formalism.IndefR.Bridge.Gf V} (hk : k ∈ (levEnv V β L).J)
    (e : (finHom V).rangeRestrict h' = Formalism.IndefR.Bridge.ratF V γ * (finHom V).rangeRestrict h * k) :
    clsA V (lev D.sp.cm V.gram β (flag1L L)) h' = clsA V (lev D.sp.cm V.gram β (flag1L L)) h := by
  obtain ⟨κ, hκ⟩ := MonoidHom.mem_range.1 k.2
  have h1 := finE_of_eq hκ e
  have h2 := finE_mem_lev hκ hk
  obtain ⟨κ', hκ'G, hκ'⟩ := AdelCls.exists_fin V (finU V κ)
  refine (((AdelCls.adelic_classes D V).2.2.2.2 _ h h').2 ⟨γ, γ.2, κ', ?_, (↑γ * h * κ')⁻¹ * h', ?_, by group⟩).symm
  · refine Formalism.IndefR.Lev.mem_levA.2 ⟨hκ'G, ?_⟩
    rw [← coe_finU, hκ', coe_finU]
    exact h2
  · refine (AdelCls.finU_eq_one_iff V _).1 ?_
    apply Subtype.ext
    have h1' : finE V h' = finE V ↑γ * finE V h * finE V κ := by
      simpa only [Subgroup.coe_mul, coe_finU] using congrArg Subtype.val h1
    have hκ'' : finE V κ' = finE V κ := by
      simpa only [coe_finU] using congrArg Subtype.val hκ'
    rw [coe_finU, OneMemClass.coe_one]
    simp only [map_mul, map_inv, h1', hκ'']
    group

theorem clsA_eq_of_eq {h h' : GA D V} {γ : GQ V} {k : Formalism.IndefR.Bridge.Gf V} (hk : k ∈ (levEnv V β L).J)
    (e : (finHom V).rangeRestrict h' = Formalism.IndefR.Bridge.ratF V γ * (finHom V).rangeRestrict h * k) :
    clsA V (lev D.sp.cm V.gram β (flag1L L)) h' = clsA V (lev D.sp.cm V.gram β (flag1L L)) h := by
  exact clsA_eq_of_ratF_mul hk e

theorem exists_form_value (c : CoefA V) (hχ : ∀ x, levFn β (flag1L L) x = 1)
    (hG : ∀ c₀ : Cl D.sp.cm V.gram (lev D.sp.cm V.gram β (flag1L L)), Gam c₀ = ⊥) (h : GA D V) (w : c.W) :
    ∃ f : Formalism.IndefR.Bridge.Gf V → c.W,
      f ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ ∧
      f ((finHom V).rangeRestrict h) = w ∧
      ∀ h' : GA D V, clsA V (lev D.sp.cm V.gram β (flag1L L)) h' ≠ clsA V (lev D.sp.cm V.gram β (flag1L L)) h →
        f ((finHom V).rangeRestrict h') = 0 := by
  have hχ' : ∀ q, (levEnv V β L).χ q = 1 := fun q => hχ _
  obtain ⟨f, hf, hfx, hf0⟩ := exists_adForms_value (W := c.W) (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J
    (levEnv V β L).χ hχ' ((finHom V).rangeRestrict h) (fun γ q hq e => stab_trivial hG h γ q hq e) w
  refine ⟨f, hf, hfx, fun h' hne => hf0 _ ?_⟩
  rintro ⟨γ, q, hq, e⟩
  exact hne (clsA_eq_of_eq hq e)

set_option maxHeartbeats 1000000 in
private theorem apply_rangeRestrict_mul_eq_of_mem_adForms_of_mem_levS {c : CoefA V} (hχ : ∀ x, levFn β (flag1L L) x = 1) {f : Formalism.IndefR.Bridge.Gf V → c.W}
    (hf : f ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
    (g : GA D V) {k : GA D V} (hk : k ∈ levS V β (flag1L L)) :
    f ((finHom V).rangeRestrict (g * k)) = f ((finHom V).rangeRestrict g) := by
  have hf' : ∀ (γ : GQ V) (x : Formalism.IndefR.Bridge.Gf V) (q : (levEnv V β L).J),
      f (Formalism.IndefR.Bridge.ratF V γ * x * q) = ((levEnv V β L).χ q : ℂ) • c.coef.ρ γ (f x) := hf
  have hk0 : k ∈ levA V (lev D.sp.cm V.gram β (flag1L L)) := hk
  have hk' : finE V k ∈ lev D.sp.cm V.gram β (flag1L L) := (Formalism.IndefR.Lev.mem_levA.1 hk0).2
  have hJ : (finHom V).rangeRestrict k ∈ (levEnv V β L).J := by
    show Formalism.UG.bc (swapAE D) (finHom V k) ∈ lev D.sp.cm V.gram β (flag1L L)
    rw [← finE_eq]
    exact hk'
  have e1 := hf' 1 ((finHom V).rangeRestrict g) ⟨_, hJ⟩
  have hc1 : (levEnv V β L).χ ⟨_, hJ⟩ = 1 := hχ (Formalism.UG.bc (swapAE D) (finHom V k))
  rw [map_one, one_mul, map_one, hc1, Units.val_one, one_smul] at e1
  rw [map_mul]
  exact e1

theorem form_mul_level {c : CoefA V} (hχ : ∀ x, levFn β (flag1L L) x = 1) {f : Formalism.IndefR.Bridge.Gf V → c.W}
    (hf : f ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
    (g : GA D V) {k : GA D V} (hk : k ∈ levS V β (flag1L L)) :
    f ((finHom V).rangeRestrict (g * k)) = f ((finHom V).rangeRestrict g) := by
  exact apply_rangeRestrict_mul_eq_of_mem_adForms_of_mem_levS hχ hf g hk

theorem toMap_apply {S : D.what₂.Tau → SPar} {M : DSModel V S} (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ)
    (f : Formalism.IndefR.Bridge.Gf V → c.W) (v : M.Vec) (g : GA D V) : PiTensorProduct.lift.symm (c.toMap pr f) v g =
      pr (c.ρ g⁻¹ (f ((finHom V).rangeRestrict g))) (PiTensorProduct.tprod ℂ v) := rfl

set_option maxHeartbeats 1000000 in
private theorem exists_mult_evAt_eq_and_vanish_off_class : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank), IsInfFam θ → V.SigOK → V.IsDefinite → c.Is → IsDualPair θ M c pr → Function.Surjective pr → (∀ x, levFn β (flag1L L) x = 1) → (∀ c₀ : Cl D.sp.cm V.gram (lev D.sp.cm V.gram β (flag1L L)), Gam c₀ = ⊥) → ∀ (h : GA D V) (ℓ : MultilinearMap ℂ (fun τ : D.what₂.Tau => M.sm τ) ℂ), ∃ T ∈ Mult θ M (levS V β (flag1L L)) (levChi V β (flag1L L)), evAt M h T = ℓ ∧ ∀ h' : GA D V, clsA V (lev D.sp.cm V.gram β (flag1L L)) h' ≠ clsA V (lev D.sp.cm V.gram β (flag1L L)) h → evAt M h' T = 0 := by
  intro D θ V S M c pr β L hθ hs hd hc hpr hsurj hχ hG h ℓ
  obtain ⟨w, hw⟩ := hsurj (PiTensorProduct.lift ℓ)
  obtain ⟨f, hf, hfx, hf0⟩ := exists_form_value c hχ hG h (c.ρ h w)
  have hM := GlobalTheory.DefiniteEnd.isMultMap_toMap hθ hs hd M hc hpr hf
  have hval : ∀ (v : M.Vec) (g : GA D V), PiTensorProduct.lift.symm (c.toMap pr f) v g =
      pr (c.ρ g⁻¹ (f ((finHom V).rangeRestrict g))) (PiTensorProduct.tprod ℂ v) :=
    fun v g => toMap_apply c pr f v g
  have hinv : c.ρ h⁻¹ (c.ρ h w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  refine ⟨PiTensorProduct.lift.symm (c.toMap pr f), Submodule.subset_span ?_, ?_, ?_⟩
  · show IsMultMap θ M (levS V β (flag1L L)) (levChi V β (flag1L L)) _
    refine { hM with lev := ?_ }
    intro v k hk g
    have hk0 : k ∈ levA V (lev D.sp.cm V.gram β (flag1L L)) := hk
    have hk' : k ∈ GfC V ∧ finE V k ∈ lev D.sp.cm V.gram β (flag1L L) := Formalism.IndefR.Lev.mem_levA.1 hk0
    have hchi : levChi V β (flag1L L) k = 1 := by
      show ((Formalism.L2.DIV.levFn β (flag1L L) (finE V k) : ℂˣ) : ℂ) = 1
      rw [hχ, Units.val_one]
    have hρ : c.ρ k⁻¹ = 1 := hc.1 _ ((GfC V).inv_mem hk'.1)
    rw [hval, hval, hchi, one_mul, form_mul_level hχ hf g hk, mul_inv_rev, map_mul, Module.End.mul_apply, hρ,
      Module.End.one_apply]
  · ext v
    rw [evAt_apply, hval, hfx, hinv, hw, PiTensorProduct.lift.tprod]
  · intro h' hne
    ext v
    rw [evAt_apply, hval, hf0 h' hne, map_zero, map_zero, LinearMap.zero_apply, MultilinearMap.zero_apply]

end

theorem exists_mult_value : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank), IsInfFam θ → V.SigOK → V.IsDefinite → c.Is → IsDualPair θ M c pr → Function.Surjective pr → (∀ x, levFn β (flag1L L) x = 1) → (∀ c₀ : Cl D.sp.cm V.gram (lev D.sp.cm V.gram β (flag1L L)), Gam c₀ = ⊥) → ∀ (h : GA D V) (ℓ : MultilinearMap ℂ (fun τ : D.what₂.Tau => M.sm τ) ℂ), ∃ T ∈ Mult θ M (levS V β (flag1L L)) (levChi V β (flag1L L)), evAt M h T = ℓ ∧ ∀ h' : GA D V, clsA V (lev D.sp.cm V.gram β (flag1L L)) h' ≠ clsA V (lev D.sp.cm V.gram β (flag1L L)) h → evAt M h' T = 0 := by
  exact exists_mult_evAt_eq_and_vanish_off_class

end GlobalTheory.DefFree

end
