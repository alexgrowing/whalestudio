import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfConjMemOfPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClPlusAndExistsCoords
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus posDef_dual Cols levPlus mem_cols)

namespace GlobalTheory.RowTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

section Generic

variable {G Γ W Cl ι : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Finite Cl]

open Classical in

theorem eq_adForms_of_values (ιG : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (y : Cl → G)
    (hdec : ∀ g, ∃ (γ : Γ) (c : Cl) (k : J), g = ιG γ * y c * k) (S : Submodule ℂ (G → W))
    (hS : S ≤ Bridge.AdForms ιG ρ J 1) (w : ι → W) (hw : Submodule.span ℂ (Set.range w) = ⊤)
    (hsingle : ∀ c i, ∃ s ∈ S, ∀ c', s (y c') = if c' = c then w i else 0) : S = Bridge.AdForms ιG ρ J 1 := by
  classical
  have : Fintype Cl := Fintype.ofFinite _
  refine le_antisymm hS fun F hF => ?_
  let ev : (G → W) →ₗ[ℂ] (Cl → W) := LinearMap.pi fun c => LinearMap.proj (y c)
  have hev : ∀ f c, ev f c = f (y c) := fun _ _ => rfl
  have hinj : ∀ f ∈ Bridge.AdForms ιG ρ J 1, ev f = 0 → f = 0 := by
    intro f hf h0
    funext g
    obtain ⟨γ, c, k, rfl⟩ := hdec g
    have h1 : f (y c) = 0 := congrFun h0 c
    have h2 := hf γ (y c) k
    rw [h2, h1, map_zero, smul_zero]
    rfl
  have hsurj : S.map ev = ⊤ := by
    refine eq_top_iff.2 fun f _ => ?_
    rw [← Finset.univ_sum_single f]
    refine Submodule.sum_mem _ fun c _ => ?_
    have hfc : f c ∈ Submodule.span ℂ (Set.range w) := by rw [hw]; trivial
    have e : Pi.single c (f c) = LinearMap.single ℂ (fun _ : Cl => W) c (f c) := rfl
    rw [e]
    refine Submodule.mem_comap.1 (((Submodule.span_le (p := (S.map ev).comap (LinearMap.single ℂ (fun _ : Cl => W) c))).2 ?_) hfc)
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hsv⟩ := hsingle c i
    refine Submodule.mem_comap.2 ⟨s, hs, funext fun c' => ?_⟩
    rw [hev, hsv]
    by_cases h : c' = c
    · subst h; simp
    · simp [h]
  obtain ⟨s, hs, hse⟩ : ev F ∈ S.map ev := by rw [hsurj]; trivial
  have h0 : F - s = 0 := hinj _ (sub_mem hF (hS hs)) (by rw [map_sub, hse, sub_self])
  rwa [sub_eq_zero.1 h0]

end Generic

section Reps

variable {T' : Type} {L : LevCh D T'} {sc : Consts} {G : GridData L sc}

theorem exists_gf_reps (rp : ClassReps G) :
    ∃ y : G.ClPlus → Bridge.Gf (G.V (.top 0)),
      (∀ c, Formalism.UG.bc (Lev.swapAE D) ((y c : Bridge.Gf (G.V (.top 0))) : GL _ _) = (rp.x c : GLf G)) ∧
      ∀ g : Bridge.Gf (G.V (.top 0)), ∃ (γ : GQ (G.V (.top 0))) (c : G.ClPlus) (k : levPlus G),
        g = Bridge.ratF (G.V (.top 0)) γ * y c * k := by
  obtain ⟨hfin, -, -, -, hcl⟩ := GlobalTheory.DefFree.AdelCls.adelic_classes D (G.V (.top 0))
  choose h _ hh using fun c => hfin (rp.x c)
  refine ⟨fun c => (finHom (G.V (.top 0))).rangeRestrict (h c), fun c => ?_, fun g => ?_⟩
  · have := congrArg Subtype.val (hh c)
    exact this
  · have hg0 : ∃ h0 : GA D (G.V (.top 0)), finHom (G.V (.top 0)) h0 = g.1 := g.2
    obtain ⟨h0, hg⟩ := hg0
    have hc : GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus (h (GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0)) =
        GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0 := by
      show (Quotient.mk'' (GlobalTheory.DefFree.finU (G.V (.top 0)) (h (GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0))) :
        Cl D.sp.cm (G.V (.top 0)).gram G.Kplus) = _
      rw [hh]
      exact rp.classRepresentative_mk _
    have hx := (hcl G.Kplus (h (GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0)) h0).1 hc
    obtain ⟨γ, hγ, hx⟩ := hx
    obtain ⟨κ, hκ, k, hk, e⟩ := hx
    have hκ' : (finHom (G.V (.top 0))).rangeRestrict κ ∈ levPlus G := by
      show Formalism.UG.bc (Lev.swapAE D) (finHom (G.V (.top 0)) κ) ∈ G.Kplus
      exact hκ.2
    refine ⟨⟨γ, hγ⟩, GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0, ⟨_, hκ'⟩, Subtype.ext ?_⟩
    have hk1 : finHom (G.V (.top 0)) k = 1 := hk
    show g.1 = finHom (G.V (.top 0)) γ * finHom (G.V (.top 0)) (h (GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0)) *
      finHom (G.V (.top 0)) κ
    have e2 := congrArg (finHom (G.V (.top 0))) e
    simp only [map_mul (finHom (G.V (.top 0))), hk1, mul_one] at e2
    exact hg.symm.trans e2

open Classical in

theorem span_colOf_psi {θ : InfFam D} (hθ : IsInfFam θ) (rp : ClassReps G) {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G))
    (Φ : G.Datum) :
    Submodule.span ℂ ((fun a => colOf θ (psi rp e a)) '' {a | datumOf e a = Φ}) = Cols G θ := by
  classical
  obtain ⟨y, hy, hdec⟩ := exists_gf_reps rp
  have hspan : Submodule.span ℂ (Set.range fun i => GlobalTheory.CoefModel.toHilb (LaP G) (posDef_dual G)
      (GlobalTheory.CoefModel.mapVV D.what₂.embLL (LaP G) (bVV D.what₂.LL (LaP G) i))) = ⊤ := by
    have := congrArg (Submodule.map (GlobalTheory.CoefModel.toHilb (LaP G) (posDef_dual G)).toLinearMap)
      (GlobalTheory.CoefModel.span_mapVV D.what₂.embLL (LaP G))
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range, ← Set.range_comp] at this
    exact this
  refine eq_adForms_of_values (W := (coefPlus G θ).W) (Bridge.ratF (G.V (.top 0))) (coefPlus G θ).coef.ρ
    (levPlus G) y hdec _ ?_ _ hspan fun c i => ?_
  · rw [Submodule.span_le]
    rintro _ ⟨a, -, rfl⟩
    exact colOf_mem hθ (psi_left _ _ a) fun g _ hk => psi_right _ _ a g hk
  · refine ⟨colOf θ (psi rp e (e.symm ((Φ, c), i))), Submodule.subset_span ⟨_, ?_, rfl⟩, fun c' => ?_⟩
    · show (e (e.symm ((Φ, c), i))).1.1 = Φ
      rw [Equiv.apply_symm_apply]
    · unfold colOf psi
      rw [hy c', Equiv.apply_symm_apply, rp.gridClassReps_delta_apply_rep (ClassReps.neat rp)]
      by_cases h : c' = c <;> simp [h] <;> rfl

end Reps

variable (ch : Choice R)

theorem span_col_eq_cols (Φ : ch.G.Datum) :
    Submodule.span ℂ (ch.col '' {a | ch.Phi a = Φ}) = Cols ch.G ch.W.θ :=
  span_colOf_psi ch.W.θ_is ch.rp ch.e Φ

end GlobalTheory.RowTest

end
