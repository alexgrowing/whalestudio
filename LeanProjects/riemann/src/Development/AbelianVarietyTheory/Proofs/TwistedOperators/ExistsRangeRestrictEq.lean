import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TranslateRepresentations
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateUnitaryLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormGoodRowsFiniteGroupActionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLiftFormsFiniteGroupActionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftLowestKTypeCompatibility
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftEquivariance

theorem commutes_adjoint {G E E' : Type} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E']
    (ρ : Representation ℂ G E) (ρ' : Representation ℂ G E') (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (hρ' : ∀ g x, ‖ρ' g x‖ = ‖x‖)
    (f : E →ₗ[ℂ] E') (hf : Commutes ρ ρ' f) : Commutes ρ' ρ (LinearMap.adjoint f) := by
  intro g y
  have i1 : ∀ u v, inner ℂ (ρ g u) (ρ g v) = inner ℂ u v :=
    fun u v => (LinearIsometry.mk (ρ g) (hρ g)).inner_map_map u v
  have i2 : ∀ u v, inner ℂ (ρ' g u) (ρ' g v) = inner ℂ u v :=
    fun u v => (LinearIsometry.mk (ρ' g) (hρ' g)).inner_map_map u v
  refine ext_inner_left ℂ fun x => ?_
  have e : x = ρ g (ρ g⁻¹ x) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [e, i1, LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right, hf g, i2]

section Generic

variable {Γ Gf W G : Type} [Group Γ] [Group Gf] [Group G] [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem translate_indep (ι : Γ →* Gf) (ρ : Γ →* Module.End ℂ W) (l : Bridge.LevDatG Gf) {F : Gf → W}
    (hF : F ∈ Bridge.AdForms ι ρ l.J l.χ) (κ κ' : l.Q) (hk : ((κ⁻¹ * κ' : l.Q) : Gf) ∈ l.J) (h : Gf) :
    (((l.ch κ')⁻¹ : ℂˣ) : ℂ) • F (h * κ') = (((l.ch κ)⁻¹ : ℂˣ) : ℂ) • F (h * κ) := by
  have e := hF 1 (h * κ) ⟨_, hk⟩
  have e1 : ι 1 * (h * κ) * ((κ⁻¹ * κ' : l.Q) : Gf) = h * κ' := by simp [mul_assoc]
  have e2 : l.χ ⟨_, hk⟩ = (l.ch κ)⁻¹ * l.ch κ' := by
    rw [← l.ch_J, ← map_inv, ← map_mul]
  simp only at e
  rw [e1, e2, map_one, Module.End.one_apply] at e
  rw [e, smul_smul, ← Units.val_mul, mul_comm (l.ch κ)⁻¹, inv_mul_cancel_left]

theorem exists_rep (ι : Γ →* Gf) (ρ : Γ →* Module.End ℂ W) (l : Bridge.LevDatG Gf) (M : HMod (Gf → W))
    (hinj : Function.Injective M.e) (hM : ∀ x, M.e x ∈ Bridge.AdForms ι ρ l.J l.χ)
    (hT : ∀ (κ : l.Q) (x : M.H), ∃ x' : M.H, (∀ h, M.e x' h = ((l.ch κ : ℂˣ) : ℂ)⁻¹ • M.e x (h * κ)) ∧ ‖x'‖ = ‖x‖)
    (red : l.Q →* G) (hs : Function.Surjective red) (hker : ∀ κ, red κ = 1 → (κ : Gf) ∈ l.J) :
    ∃ π : Representation ℂ G M.H, (∀ g x, ‖π g x‖ = ‖x‖) ∧
      ∀ κ x h, M.e (π (red κ) x) h = (((l.ch κ)⁻¹ : ℂˣ) : ℂ) • M.e x (h * κ) := by
  choose s hs using hs
  choose T hT hn using hT
  have key : ∀ κ x h, M.e (T (s (red κ)) x) h = (((l.ch κ)⁻¹ : ℂˣ) : ℂ) • M.e x (h * κ) := fun κ x h => by
    rw [hT, ← Units.val_inv_eq_inv_val]
    exact translate_indep ι ρ l (hM x) κ _ (hker _ (by rw [map_mul, map_inv, hs, inv_mul_cancel])) h
  let L : G → M.H →ₗ[ℂ] M.H := fun g =>
    { toFun := T (s g)
      map_add' := fun x y => hinj (funext fun h => by
        rw [map_add, Pi.add_apply, hT, hT, hT, map_add, Pi.add_apply, smul_add])
      map_smul' := fun a x => hinj (funext fun h => by
        rw [map_smul, Pi.smul_apply, hT, hT, map_smul, Pi.smul_apply, smul_comm]; rfl) }
  refine ⟨{ toFun := L, map_one' := ?_, map_mul' := fun g g' => ?_ }, fun g x => hn _ x, key⟩
  · ext x
    refine hinj (funext fun h => ?_)
    have := key 1 x h
    rw [map_one] at this
    exact this.trans (by simp)
  · ext x
    refine hinj (funext fun h => ?_)
    have := key (s g * s g') x h
    rw [map_mul, hs, hs] at this
    refine this.trans ?_
    show _ = M.e (T (s g) (T (s g') x)) h
    rw [hT, hT, smul_smul, map_mul, Subgroup.coe_mul, mul_assoc]
    simp [mul_comm]

end Generic

variable {D : D7}

theorem mem_parLev {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {x : Bridge.Gf V}
    (h : x ∈ (levEnv V β L).Q) : Formalism.UG.bc (swapAE D) x.1 ∈ parLev D.sp.cm V.gram β L := by
  have h1 : Formalism.UG.bc (swapAE D) x.1 ∈ lev D.sp.cm V.gram β (flagL L) := h
  exact h1.1

theorem mem_J {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {x : Bridge.Gf V}
    (h : x ∈ (levEnv V β L).Q) (h1 : rTup β L (Formalism.UG.bc (swapAE D) x.1) = 1) : x ∈ (levEnv V β L).J := by
  have h2 : rTup β L (Formalism.UG.bc (swapAE D) x.1) ∈ (⊥ : Subgroup (G0 L.Pg L.r)) := Subgroup.mem_bot.2 h1
  have h3 : Formalism.UG.bc (swapAE D) x.1 ∈ lev D.sp.cm V.gram β (flag1L L) := ⟨mem_parLev h, h2⟩
  exact h3

theorem rTup_bc_mul {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {x y : Bridge.Gf V}
    (hx : x ∈ (levEnv V β L).Q) (hy : y ∈ (levEnv V β L).Q) :
    rTup β L (Formalism.UG.bc (swapAE D) (x * y).1) =
      rTup β L (Formalism.UG.bc (swapAE D) x.1) * rTup β L (Formalism.UG.bc (swapAE D) y.1) := by
  rw [Subgroup.coe_mul, map_mul]
  exact rTup_mul (mem_parLev hx) (mem_parLev hy)

def redHom (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    (levEnv V β L).Q →* G0 L.Pg L.r :=
  MonoidHom.mk' (fun κ => rTup β L (Formalism.UG.bc (swapAE D) κ.1.1)) fun a b => rTup_bc_mul a.2 b.2

theorem redHom_eq {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {κ : (levEnv V β L).Q}
    {g₀ : G0 L.Pg L.r} : LiftsTo V β L κ g₀ ↔ redHom V β L κ = g₀ := Iff.rfl

theorem exists_transRep (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (c : CoefA V) (hc : c.Is)
    (M : HMod (Bridge.Gf V → c.W)) {I : Type} [Fintype I] (y : I → Bridge.Gf V)
    (hy : Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y)
    (hM : M.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
      (Bridge.adInner (Bridge.ratF V) (levEnv V β L).J y))
    {G : Type} [Group G] (eG : G ≃* G0 L.Pg L.r) (hs : ∀ g, ∃ κ, LiftsTo V β L κ (eG g)) :
    ∃ π : Representation ℂ G M.H, (∀ g x, ‖π g x‖ = ‖x‖) ∧ IsTransRep V β L eG M π := by
  have hred : ∀ κ g, LiftsTo V β L κ (eG g) → (eG.symm.toMonoidHom.comp (redHom V β L)) κ = g := fun κ g h =>
    eG.symm_apply_eq.2 (redHom_eq.1 h)
  have h1 : ∀ x, M.e x ∈ Bridge.AdForms (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L).J (levEnv V β L).χ :=
    fun x => hM.2.1.le ⟨x, rfl⟩
  have h2 := ClassSumTranslate.translate_model (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L)
    (fun γ u v => hc.2.1 _ u v) (ClassSumTranslate.levEnv_normal V β L) (fun q => ClassSumTranslate.norm_levFn V β L _) hy M hM
  have h3 : Function.Surjective (eG.symm.toMonoidHom.comp (redHom V β L)) := fun g => (hs g).imp fun κ h => hred κ g h
  have h4 : ∀ κ, (eG.symm.toMonoidHom.comp (redHom V β L)) κ = 1 → (κ : Bridge.Gf V) ∈ (levEnv V β L).J := fun κ h =>
    mem_J κ.2 (redHom_eq.2 (eG.symm.injective (h.trans (map_one eG.symm).symm)))
  refine (exists_rep (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L) M hM.1 h1 h2 _ h3 h4).imp
    fun π hπ => ⟨hπ.1, fun g x => ⟨hs g, fun κ hκ h => ?_⟩⟩
  exact (congrArg (fun g' => M.e (π g' x) h) (hred κ g hκ)).symm.trans (hπ.2 κ x h)

theorem exists_rangeRestrict_eq {G H : Type} [Group G] [Group H] (f : G →* H) (K : Subgroup G)
    (h : ∀ g, ∃ a ∈ f.ker, ∃ k ∈ K, g = a * k) (x : f.range) : ∃ k ∈ K, f.rangeRestrict k = x := by
  obtain ⟨_, g, rfl⟩ := x
  obtain ⟨a, ha, k, hk, rfl⟩ := h g
  refine ⟨k, hk, Subtype.ext ?_⟩
  show f k = f (a * k)
  rw [map_mul, MonoidHom.mem_ker.1 ha, one_mul]

theorem exists_fin_lift (V : HSp D) (x : Bridge.Gf V) : ∃ k ∈ GfC V, (finHom V).rangeRestrict k = x :=
  exists_rangeRestrict_eq (finHom V) (GfC V) (GlobalTheory.UnitarySplit.real_finite_split D V).1 x

theorem ch_eq {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} (q : (levEnv V β L).Q) :
    (levEnv V β L).ch q = levFn β (flagL L) (Formalism.UG.bc (swapAE D) q.1.1) := rfl

theorem exists_adelic_lift {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {g₀ : G0 L.Pg L.r} {F F' : Bridge.Gf V → W}
    (h : IsTranslate V β L g₀ F F') :
    ∃ κ, IsLevelLift V β L g₀ κ ∧ ∀ x, F' x = (levChi V β (flagL L) κ)⁻¹ • F (x * (finHom V).rangeRestrict κ) := by
  refine h.1.elim fun q hl => (exists_fin_lift V q.1).imp fun k hk => ?_
  have e0 : finHom V k = q.1.1 := congrArg Subtype.val hk.2
  have e1 : finE V k = Formalism.UG.bc (swapAE D) q.1.1 := (finE_eq V k).trans (congrArg (Formalism.UG.bc (swapAE D)) e0)
  have hl1 : rTup β L (Formalism.UG.bc (swapAE D) q.1.1) = g₀ := hl
  have hc : levChi V β (flagL L) k = (((levEnv V β L).ch q : ℂˣ) : ℂ) :=
    congrArg Units.val ((congrArg (levFn β (flagL L)) e1).trans (ch_eq q).symm)
  have hp : finE V k ∈ parLev D.sp.cm V.gram β L := e1.symm ▸ mem_parLev q.2
  refine ⟨⟨hk.1, hp, (congrArg (rTup β L) e1).trans hl1⟩, fun x => (h.2 q hl x).trans ?_⟩
  exact congrArg₂ (fun (a : ℂ) (z : Bridge.Gf V) => a • F (x * z))
    ((Units.val_inv_eq_inv_val _).trans (congrArg (·⁻¹) hc.symm)) hk.2.symm

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

end GlobalTheory.LiftEquivariance

end
