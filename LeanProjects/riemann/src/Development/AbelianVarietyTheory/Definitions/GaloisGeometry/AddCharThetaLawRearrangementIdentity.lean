import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Divisors.MemStdLatticeIffIntegralCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelCoefficientSpaceRealPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCongruenceInLevelCharacterOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyFiniteTypeIndexOfRowsPos
import Formalism.LocalToGlobal.IndefiniteReal.RealRecPins

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.MainNotions.N IsDedekindDomain NumberField
open Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NJoin.Inh

section Frame

variable {D : D7} {V : HSp D} {n : ℕ} (P : RowPsi V n)

def finP : Formalism.AUTREP.GAf D.host.E n →* Bridge.Gf V := (finHom V).rangeRestrict.comp P.ψ

theorem finitePart_surjective : Function.Surjective (finP P) := by
  rintro ⟨_, g, rfl⟩
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g)
  obtain ⟨h, rfl⟩ := P.onto k k1
  exact ⟨h, Subtype.ext k2⟩

theorem finitePart_injective : Function.Injective (finP P) := fun a b h =>
  P.inj (GlobalTheory.UnitarySplit.ga_ext V ((show infHom V (P.ψ a) = 1 from P.into a).trans (show infHom V (P.ψ b) = 1 from P.into b).symm)
    (congrArg Subtype.val h))

variable (c : CoefA V)

theorem ext_psi (hc : ∀ h ∈ GfC V, c.ρ h = 1) (φ : Bridge.Gf V → c.W) (h : Formalism.AUTREP.GAf D.host.E n) :
    c.ext φ (P.ψ h) = φ (finP P h) := by
  show c.ρ (P.ψ h)⁻¹ (φ (finP P h)) = _
  rw [hc _ ((GfC V).inv_mem (P.into h))]
  rfl

variable (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank)

def levJ : Subgroup (Formalism.AUTREP.GAf D.host.E n) := (levG V β L).comap P.ψ

def levX : levJ P β L →* ℂˣ :=
  (levChar D.sp.cm V.gram β L).comp (((finE V).comp (P.ψ.comp (levJ P β L).subtype)).codRestrict _ fun κ => κ.2.2)

theorem mem_levi_flag_of_mem_parabolic {x : GL (Fin V.rank) (EAf D)} (hx : x ∈ lev D.sp.cm V.gram β (flag1L L)) :
    x ∈ lev D.sp.cm V.gram β L ∧ levFn β (flag1L L) x = levFn β L x := by
  have e : rTup β L x = 1 := hx.2
  refine ⟨⟨hx.1, e ▸ one_mem _⟩, ?_⟩
  have h1 := levFn_withP (V := V) (β := β) (L := L) L.P x
  rw [e, blockDiagonalExtendByOnePrimeField_one, one_mul] at h1
  rw [levFn_flag1]
  exact h1.symm

variable {W : Type} [AddCommGroup W] [Module ℂ W] (e : c.W ≃ₗ[ℂ] W)

def rd : (GA D V → c.W) →ₗ[ℂ] (Formalism.AUTREP.GAf D.host.E n → W) where
  toFun F h := e (F (P.ψ h))
  map_add' _ _ := funext fun _ => map_add e _ _
  map_smul' _ _ := funext fun _ => map_smul e _ _

def forms : Submodule ℂ (GA D V → c.W) :=
  (Bridge.AdForms (Bridge.ratF V) (c.ρ.comp (Formalism.L2.Theta.GQ V).subtype) (levEnv V β L).J (levEnv V β L).χ).map c.ext ⊓
    levSubV V c.W (levS V β L) (levChi V β L)

theorem rd_ext_eq_zero (hc : ∀ h ∈ GfC V, c.ρ h = 1) (φ : Bridge.Gf V → c.W) (h : rd P c e (c.ext φ) = 0) : c.ext φ = 0 := by
  have : φ = 0 := by
    funext x
    obtain ⟨k, rfl⟩ := finitePart_surjective P x
    rw [← ext_psi P c hc φ k]
    exact e.map_eq_zero_iff.1 (congrFun h k)
  rw [this, map_zero]

theorem adForms_left {G Γ W : Type} [Group G] [Group Γ] (ι : Γ →* G) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {φ : G → W} (hm : φ ∈ Bridge.AdForms ι ρ J χ) (γ : Γ) (h : G) :
    φ (ι γ * h) = ρ γ (φ h) := by
  simpa using hm γ h 1

theorem rho_inv_mul {G M : Type} [Group G] [Monoid M] (ρ : G →* M) (g k : G) (h : ρ k⁻¹ = 1) : ρ (g * k)⁻¹ = ρ g⁻¹ := by
  rw [mul_inv_rev, map_mul, h, one_mul]

theorem wachExpansion_smul_compatible {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (e : M ≃ₗ[ℂ] N) {a b : Module.End ℂ M}
    {x y : N} {z : ℂ} (h1 : a = b) (h2 : x = z • y) : a (e.symm x) = z • b (e.symm y) := by
  rw [h1, h2, map_smul, map_smul]

theorem addChar_theta_law_rearrangement_identity {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (e : M ≃ₗ[ℂ] N) {a : Module.End ℂ M}
    {b : Module.End ℂ N} (h : ∀ v, e (a v) = b (e v)) {x y : N} {z z' : ℂ} (hz : z' = z) (h2 : x = z • b y) :
    e.symm x = z' • a (e.symm y) := by
  apply e.injective
  rw [map_smul, h, e.apply_symm_apply, e.apply_symm_apply, h2, hz]

theorem exists_section {A B : Type} [Group A] [Group B] (f : A →* B) (h1 : Function.Injective f) (h2 : Function.Surjective f) :
    ∃ s : B →* A, (∀ x, f (s x) = x) ∧ ∀ a, s (f a) = a :=
  ⟨(MulEquiv.ofBijective f ⟨h1, h2⟩).symm.toMonoidHom, (MulEquiv.ofBijective f ⟨h1, h2⟩).apply_symm_apply,
    (MulEquiv.ofBijective f ⟨h1, h2⟩).symm_apply_apply⟩

variable (hc : ∀ h ∈ GfC V, c.ρ h = 1) (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ D.host.E n) W)
  (rat : ∀ h, h ∈ ReciprocityTheory.Aut.GQ D.host.E n ↔ ∃ γ ∈ Formalism.L2.Theta.GQ V, finHom V γ = finHom V (P.ψ h))
  (wt : ∀ (h : ReciprocityTheory.Aut.GQ D.host.E n), ∀ γ ∈ Formalism.L2.Theta.GQ V, finHom V γ = finHom V (P.ψ h) →
    ∀ v, e (c.ρ γ v) = ρ h (e v))
include hc rat wt

theorem rd_left {J : Subgroup (Bridge.Gf V)} {χ : J →* ℂˣ} {φ : Bridge.Gf V → c.W}
    (hφ : φ ∈ Bridge.AdForms (Bridge.ratF V) (c.ρ.comp (Formalism.L2.Theta.GQ V).subtype) J χ) (h : ReciprocityTheory.Aut.GQ D.host.E n) (g : Formalism.AUTREP.GAf D.host.E n) :
    rd P c e (c.ext φ) (h * g) = ρ h (rd P c e (c.ext φ) g) := by
  obtain ⟨γ, hγ, eq⟩ := (rat h).1 h.2
  have e1 : finP P h = Bridge.ratF V ⟨γ, hγ⟩ := Subtype.ext eq.symm
  have e2 : finP P (h * g) = Bridge.ratF V ⟨γ, hγ⟩ * finP P g :=
    (map_mul (finP P) _ _).trans (congrArg (fun z => z * finP P g) e1)
  have e3 : φ (finP P (h * g)) = c.ρ γ (φ (finP P g)) := (congrArg φ e2).trans (adForms_left _ hφ ⟨γ, hγ⟩ (finP P g))
  have e4 : e (c.ext φ (P.ψ (h * g))) = e (c.ρ γ (φ (finP P g))) := congrArg e ((ext_psi P c hc φ _).trans e3)
  have e5 : ρ h (e (φ (finP P g))) = ρ h (e (c.ext φ (P.ψ g))) := congrArg (fun z => ρ h (e z)) (ext_psi P c hc φ g).symm
  exact e4.trans ((wt h γ hγ eq _).trans e5)

theorem map_forms_le (hL : principalLevelFrame.LevOK P (levS V β L) (levChi V β L)) :
    (forms c β L).map (rd P c e) ≤ NG.TypeSp ρ (levJ P β L) (levX P β L) := by
  rintro _ ⟨F, ⟨⟨φ, hφ, rfl⟩, hF⟩, rfl⟩
  have hF' : ∀ (κ g : Formalism.AUTREP.GAf D.host.E n), P.ψ κ ∈ levS V β L →
      rd P c e (c.ext φ) (g * κ) = levChi V β L (P.ψ κ) • rd P c e (c.ext φ) g := fun κ g hκ =>
    (congrArg (fun z => e (c.ext φ z)) (map_mul P.ψ g κ)).trans ((congrArg e (hF _ hκ _)).trans (map_smul e _ _))
  refine ⟨⟨rd_left P c e hc ρ rat wt hφ, ?_⟩, fun κ => funext fun g => hF' κ g κ.2⟩
  obtain ⟨N, hN, h⟩ := hL
  exact ⟨N, hN, fun κ hκ g => by rw [hF' κ g (h κ hκ).1, (h κ hκ).2, one_smul]⟩

omit hc in

theorem mem_adForms {f : Formalism.AUTREP.GAf D.host.E n → W} (hf : f ∈ NG.TypeSp ρ (levJ P β L) (levX P β L))
    (s : Bridge.Gf V →* Formalism.AUTREP.GAf D.host.E n) (hs : ∀ x, finP P (s x) = x) :
    (fun x => e.symm (f (s x))) ∈ Bridge.AdForms (Bridge.ratF V) (c.ρ.comp (Formalism.L2.Theta.GQ V).subtype) (levEnv V β L).J (levEnv V β L).χ := by
  intro γ x k
  have h2 : ∀ (κ : levJ P β L) g, f (g * κ) = levChi V β L (P.ψ κ) • f g := fun κ g => congrFun (hf.2 κ) g
  have ek : finE V (P.ψ (s k)) = Formalism.UG.bc (swapAE D) k.1.1 :=
    congrArg (fun z : Bridge.Gf V => Formalism.UG.bc (swapAE D) z.1) (hs k)
  have hk := mem_levi_flag_of_mem_parabolic β L (x := Formalism.UG.bc (swapAE D) k.1.1) k.2
  have hk1 : finE V (P.ψ (s k)) ∈ lev D.sp.cm V.gram β L := ek ▸ hk.1
  have hm : s k ∈ levJ P β L := ⟨P.into _, hk1⟩
  have eγ : finHom V γ = finHom V (P.ψ (s (Bridge.ratF V γ))) := (congrArg Subtype.val (hs (Bridge.ratF V γ))).symm
  have hγ : s (Bridge.ratF V γ) ∈ ReciprocityTheory.Aut.GQ D.host.E n := (rat _).2 ⟨γ, γ.2, eγ⟩
  have e0 : s (Bridge.ratF V γ * x * k) = s (Bridge.ratF V γ) * s x * s k :=
    (map_mul s _ _).trans (congrArg (fun z => z * s k) (map_mul s _ _))
  have e1 : (((levEnv V β L).χ k : ℂˣ) : ℂ) = levChi V β L (P.ψ (s k)) :=
    congrArg Units.val (hk.2.trans (congrArg (levFn β L) ek.symm))
  have e2 : f (s (Bridge.ratF V γ * x * k)) = levChi V β L (P.ψ (s k)) • ρ ⟨_, hγ⟩ (f (s x)) :=
    (congrArg f e0).trans ((h2 ⟨_, hm⟩ _).trans (congrArg _ (hf.1.1 ⟨_, hγ⟩ (s x))))
  exact addChar_theta_law_rearrangement_identity e (wt ⟨_, hγ⟩ γ γ.2 eγ) e1 e2

theorem map_forms (hL : principalLevelFrame.LevOK P (levS V β L) (levChi V β L)) :
    (forms c β L).map (rd P c e) = NG.TypeSp ρ (levJ P β L) (levX P β L) := by
  refine le_antisymm (map_forms_le P c β L e hc ρ rat wt hL) fun f hf => ?_
  obtain ⟨s, hs, hs'⟩ := exists_section (finP P) (finitePart_injective P) (finitePart_surjective P)
  refine ⟨c.ext fun x => e.symm (f (s x)), ⟨⟨_, mem_adForms P c β L e ρ rat wt hf s hs, rfl⟩, fun k hk g => ?_⟩, ?_⟩
  · obtain ⟨κ, rfl⟩ := P.onto k hk.1
    have e0 : s ((finHom V).rangeRestrict (g * P.ψ κ)) = s ((finHom V).rangeRestrict g) * κ :=
      (congrArg s (map_mul (finHom V).rangeRestrict _ _)).trans ((map_mul s _ _).trans (congrArg _ (hs' κ)))
    have e1 : c.ρ (g * P.ψ κ)⁻¹ = c.ρ g⁻¹ := rho_inv_mul c.ρ g _ (hc _ ((GfC V).inv_mem (P.into κ)))
    have e2 : f (s ((finHom V).rangeRestrict (g * P.ψ κ))) = levChi V β L (P.ψ κ) • f (s ((finHom V).rangeRestrict g)) :=
      (congrArg f e0).trans (congrFun (hf.2 ⟨κ, hk⟩) _)
    exact wachExpansion_smul_compatible e e1 e2
  · funext h
    exact (congrArg e (ext_psi P c hc _ h)).trans ((e.apply_symm_apply _).trans (congrArg f (hs' h)))

end Frame

section Algebraic

open MvPolynomial ReciprocityTheory.Aut
open scoped Matrix

variable {ι : Type} [Fintype ι] {n : ℕ}

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

end Algebraic

section Weight

variable {D : D7}

theorem rat_unit {V : HSp D} (hg : V.gram = 1) (h : Formalism.AUTREP.GAf D.host.E V.rank) :
    h ∈ ReciprocityTheory.Aut.GQ D.host.E V.rank ↔
      ∃ γ ∈ Formalism.L2.Theta.GQ V, finHom V γ = finHom V ((GlobalTheory.StdFrameModel.unitPsi hg).ψ h) := by
  have hfin : finHom V ((GlobalTheory.StdFrameModel.unitPsi hg).ψ h) = Formalism.UG.bc (GlobalTheory.StdFrameModel.sw D).symm.toRingHom h.1 :=
    (GlobalTheory.StdFrameModel.exists_lift hg h).choose_spec.2
  have hU : ∀ x : GL (Fin V.rank) D.host.E, x ∈ ReciprocityTheory.Aut.GQ0 D.host.E V.rank ↔
      x ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
    intro x
    change x.1 * ReciprocityTheory.Aut.conjT _ x.1 = 1 ↔ Formalism.UG.cT _ x.1 * V.gram * x.1 = V.gram
    rw [hg, Matrix.mul_one, mul_eq_one_comm]
    rfl
  rw [hfin]
  constructor
  · rintro ⟨x, hx, e⟩
    have hx' := (hU x).1 hx
    have hm : Formalism.UG.bc (incA D) x ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
      have h0 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x.1 * V.gram * x.1 = V.gram := hx'
      have h2 := congrArg (fun M => Matrix.map M (incA D)) h0
      simp only [Matrix.map_mul] at h2
      exact h2
    refine ⟨⟨_, hm⟩, ⟨x, hx', rfl⟩, ?_⟩
    have e' : h.1 = _ := e.symm
    rw [e']
    ext i j
    change (sndA D.host.F 1) ⊗ₜ[D.host.F] (x.1 i j) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (x.1 i j)
    rw [map_one]
  · rintro ⟨γ, ⟨x, hx, e⟩, e2⟩
    refine ⟨x, (hU x).2 hx, ?_⟩
    ext i j
    have e3 := congrArg (fun g : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => g.1 i j) e2
    have e4 : (finHom V γ).1 i j = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (x.1 i j) := by
      have e' : γ.1 = _ := e.symm
      change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) (γ.1.1 i j) = _
      rw [e']
      change (sndA D.host.F 1) ⊗ₜ[D.host.F] (x.1 i j) = _
      rw [map_one]
    simp only [e4] at e3
    apply (GlobalTheory.StdFrameModel.sw D).symm.injective
    exact e3

variable {V : HSp D} (c : CoefA V)

end Weight

section Agreement

variable {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : RealAt D cf nch tp)

theorem levOK_of_std {V : HSp D} {n : ℕ} {P : RowPsi V n} {hF : D.host.F = maximalRealSubfield D.host.E} (hP : StdFrame hF P)
    (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) : principalLevelFrame.LevOK P (levS V β L) (levChi V β L) := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.LevFinCong.exists_finCong_lev D V β L
  obtain ⟨N', hN', h'⟩ := GlobalTheory.StdFrameCong.exists_cong_finCong D V n P hF hP N hN
  exact ⟨N', hN', fun κ hκ => h _ (P.into κ) (h' κ hκ)⟩

abbrev datOf (μ : D.what₂.Tup) (j : Fin D.R.m) : LevDat D.host.E ℂ (Vc D j).rank := datVP X.R j (X.tupT μ) (X.R.levR X.F false)

theorem amt_eq (μ : D.what₂.Tup) (j : Fin D.R.m) :
    (toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj).Amt μ j = forms (X.R.cV j) (X.R.βV j) (datOf X μ j) :=
  congrArg (fun U => U ⊓ levSubV (Vc D j) (X.R.cV j).W (levS _ (X.R.βV j) (datOf X μ j)) (levChi _ (X.R.βV j) (datOf X μ j)))
    ((LinearMap.range_comp _ _).trans (congrArg (Submodule.map (X.R.cV j).ext) (X.given.core.models.HV j (X.tupT μ)).2.1))

def fnL {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) : D.what₂.Mt μ (j.1 + 1) →ₗ[ℂ] (GA D (Vc D j) → (X.R.cV j).W) where
  toFun := X.fn hμ j
  map_add' x y := congrArg Subtype.val (map_add (X.IL.jMt μ hμ j) x y)
  map_smul' a x := congrArg Subtype.val (map_smul (X.IL.jMt μ hμ j) a x)

theorem range_fnL {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) :
    LinearMap.range (fnL X hμ j) = (toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj).Amt μ j := by
  ext F
  constructor
  · rintro ⟨x, rfl⟩
    exact (X.IL.jMt μ hμ j x).2
  · intro h
    exact ⟨(X.IL.jMt μ hμ j).symm ⟨F, h⟩, congrArg Subtype.val ((X.IL.jMt μ hμ j).apply_symm_apply ⟨F, h⟩)⟩

def mtOf {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) {hF : D.host.F = maximalRealSubfield D.host.E}
    (P : RowPsi (Vc D j) D.R.nV) (hP : StdFrame hF P) (w : NG.AlgWt D.host.E D.R.nV) (e : (X.R.cV j).W ≃ₗ[ℂ] w.W)
    (rat : ∀ h, h ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV ↔ ∃ γ ∈ Formalism.L2.Theta.GQ (Vc D j), finHom (Vc D j) γ = finHom (Vc D j) (P.ψ h))
    (wt : ∀ (h : ReciprocityTheory.Aut.GQ D.host.E D.R.nV), ∀ γ ∈ Formalism.L2.Theta.GQ (Vc D j), finHom (Vc D j) γ = finHom (Vc D j) (P.ψ h) →
      ∀ v, e ((X.R.cV j).ρ γ v) = w.ρ h (e v)) : MtReal D μ (j.1 + 1) where
  wt := w
  J := levJ P (X.R.βV j) (datOf X μ j)
  χ := levX P (X.R.βV j) (datOf X μ j)
  J_open := by
    obtain ⟨N, hN, h⟩ := levOK_of_std hP (X.R.βV j) (datOf X μ j)
    exact ⟨N, hN, fun κ hκ => ⟨(h κ hκ).1, Units.ext (h κ hκ).2⟩⟩
  real := rd P (X.R.cV j) e ∘ₗ fnL X hμ j
  real_inj := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => X.fn_injective hμ j ?_
    have h : ∃ y, X.R.extV j (X.tupT μ) y = X.fn hμ j x := (X.existsUnique_vec hμ j x).exists
    obtain ⟨y, hy⟩ := h
    have h0 : rd P (X.R.cV j) e (X.R.extV j (X.tupT μ) y) = 0 := (congrArg (rd P (X.R.cV j) e) hy).trans hx
    exact (hy.symm.trans (rd_ext_eq_zero P _ e (X.given.core.models.cV j).1 _ h0)).trans
      (congrArg Subtype.val (map_zero (X.IL.jMt μ hμ j))).symm
  real_range := by
    refine Eq.trans ?_ (map_forms P _ _ _ e (X.given.core.models.cV j).1 w.ρ rat wt (levOK_of_std hP _ _))
    refine Eq.trans ?_ (congrArg (Submodule.map (rd P (X.R.cV j) e)) (amt_eq X μ j))
    exact (LinearMap.range_comp _ _).trans (congrArg (Submodule.map (rd P (X.R.cV j) e)) (range_fnL X hμ j))

end Agreement

section Reading

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {cf : CharFrame D} {nch : NChoice D}

open Classical in

def selfIdx (Xd : DivX D) : EigIdx D Xd where
  Pi := D.what₂.FT
  cOf := id
  lam_const := fun j _ _ _ e _ _ h => congrArg (fun π => Xd.logLam j π e) h

theorem xi_cast {C C' : CharFrame D} (h : C = C') (tp : TupTied D C' nch) : (h ▸ tp : TupTied D C nch).xi = tp.xi := by
  subst h
  rfl

def ofRead {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0) (tp : TupTied D cf nch)
    (hb : R.BaseW F) (hg : GlobalTheory.LiftRows.Given R F) (hf : R.FullP) (hC : R.C = cf) (hxi : ∀ t, R.xiH t = tp.xi (Y.tup t))
    (Xd : DivX D) (lab : D.what₂.FT → A3.A.fam.base.Ix) : RealAt D cf nch tp where
  G := G
  Pl0 := Pl0
  T := T
  A := A3.A
  Ks := Ks
  R := R
  F := F
  tupT := Y.tupT
  hm := Y.hm
  hTop := Y.hTop
  hinj := Y.hinj
  X0 := X0
  Ish := Y.Ish
  I0 := Y.Iz
  IL := Y.IL
  K := Y.Kc
  Xd := Xd
  E := selfIdx Xd
  labPi := lab
  PY := Y.PY
  PW := Y.PW
  eFT := Y.eFT
  piOf := fun _ _ _ => 0
  ι := Y.ιW
  Tp := hC ▸ tp
  cfEq := hC
  tpEq := by subst hC; rfl
  recR := ⟨hb, Y.tied, Y.prtE, Y.prtE0, Y.prtWE, Y.xi, fun μ hμ => by rw [xi_cast hC tp, hxi, Y.tupTie μ hμ],
    fun w => by rw [Y.muAt, Y.tupT_tup], Y.isomFin, Y.frameMatch⟩
  given := hg
  full := hf

end Reading

section Record

open Formalism.MainNotions Formalism.L2.Rows

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex}
  {Dcf : ∀ Zs : Indef.DefSub P.A3.fam3.amb3, Indef.DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : Indef.DefSub P.A3.fam3.amb3, Indef.SPer (Dcf Zs)} {Zscf : Indef.DefSub P.A3.fam3.amb3 → Indef.IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Q : RealT Rc P Dcf Spf Zscf S Ks}

def ofRealRec (Qr : RealRec Q) (hg : GlobalTheory.LiftRows.Given Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2) : RealAt D Q.Rl.C ex.nch Qr.Tp where
  G := P.Gp
  Pl0 := P.Pl0
  T := P.T
  A := P.A3.A
  Ks := Ks
  R := Q.Rl.toRealDat
  F := (faceT P Dcf Spf Zscf).lv2
  tupT := Qr.tupT
  hm := Qr.hm
  hTop := Qr.hTop
  hinj := Qr.hinj
  X0 := ex.p0
  Ish := Qr.Ish
  I0 := Qr.I0
  IL := Qr.IL
  K := Qr.Kc
  Xd := Y
  E := Qr.E
  labPi := Qr.labPi
  PY := Qr.PY
  PW := Qr.PW
  eFT := Qr.eFT
  piOf := Qr.piOf
  ι := Qr.ιW
  Tp := Qr.Tp
  cfEq := rfl
  tpEq := HEq.rfl
  recR := Qr.recR
  given := hg
  full := Q.charW.fullP

end Record

end GlobalTheory.NJoin.Inh

end
