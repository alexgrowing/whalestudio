import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsMultIPOfModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimeToHostCore
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqTie
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ThetaRead

open MeasureTheory Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.RecTie
  Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.ThetaTri
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pair

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem ipM_proj (hM : R.IsModels) (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (i : Fin D.R.m) {S U : MMap (R.MW i (sg0 D A))}
    (hS : S ∈ R.Wall i (sg0 D A)) (hU : U ∈ R.Wall i (sg0 D A)) (hfix : ∀ v, R.eWf i (sg0 D A) (S v) = S v) :
    ipM (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) S (postOn _ (R.eWf i (sg0 D A)) U) =
      ipM (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) S U ∧
    ∃ c, IsMultIP (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) S U c := by
  obtain ⟨hinj, hr, hip⟩ := hM.HW i (sg0 D A)
  obtain ⟨a, rfl⟩ : S ∈ LinearMap.range (R.HW i (sg0 D A)).e := hr ▸ hS
  obtain ⟨b, rfl⟩ : U ∈ LinearMap.range (R.HW i (sg0 D A)).e := hr ▸ hU
  refine ⟨?_, GlobalTheory.LiftLower.IsMultIP₂ (R.HW i (sg0 D A)) hip a b⟩
  have he : ∀ x, (R.HW i (sg0 D A)).e (GlobalTheory.Hk3.eH R i x) = postOn _ (R.eWf i (sg0 D A)) ((R.HW i (sg0 D A)).e x) :=
    fun x => GlobalTheory.LiftLower.e_projH hM.gW i (sg0 D A) x
  have ha : GlobalTheory.Hk3.eH R i a = a := by
    apply hinj
    rw [he]
    exact MultilinearMap.ext fun v => hfix v
  have h1 : ⟪a, GlobalTheory.Hk3.eH R i b⟫_ℂ = ⟪a, b⟫_ℂ := by
    rw [← LinearMap.adjoint_inner_left, GlobalTheory.LiftScalarL.adjoint_eH R hM hX i, ha]
  rw [hip, hip, he] at h1
  have hN : (∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun ρ _ => by exact_mod_cast (GlobalTheory.Mem.EasyInputs.dimOK D i (sg0 D A) ρ).ne'
  exact mul_left_cancel₀ hN h1

theorem mult_le_wall (F : Face D A) (b : Bool) (i : Fin D.R.m) :
    Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A))))
      (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) ≤ R.Wall i (sg0 D A) :=
  GlobalTheory.PartDims.mult_le R.θ _ fun k hk => by
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.PartDims.mem_levi_flag_of_mem_parabolic (L := R.datWp i R.triv) rfl rfl (R.levL F b (sg0 D A)) hk
    exact ⟨h1, h2.trans h3.symm⟩

end Pair

section Unit

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

abbrev emb : LowT M →ₗ[ℂ] SmT M := PiTensorProduct.map fun τ => (lowT M τ).subtype

theorem integral_kUnit (hne : ∀ τ, lowT M τ ≠ ⊥) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T U : MMap M)
    (h : ∃ c, IsMultIP M μ 𝓕 T U c) :
    ∫ g in 𝓕, star (PiTensorProduct.lift T (emb M (kUnit M)) g) * PiTensorProduct.lift U (emb M (kUnit M)) g ∂μ =
      ipM M μ 𝓕 T U := by
  have hu : ∀ τ, ∃ u : ↥(lowT M τ), ‖((u : M.sm τ) : M.H τ)‖ = 1 := by
    intro τ
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).1 (hne τ)
    have h0 : (u : M.H τ) ≠ 0 := fun h => hu0 (Submodule.coe_eq_zero.1 h)
    refine ⟨((‖(u : M.H τ)‖⁻¹ : ℝ) : ℂ) • ⟨u, hu⟩, ?_⟩
    simp only [Submodule.coe_smul, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)
  let v : M.Vec := fun τ =>
    ((Classical.epsilon fun u : ↥(lowT M τ) => ‖((u : M.sm τ) : M.H τ)‖ = 1 : ↥(lowT M τ)) : M.sm τ)
  have hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1 := fun τ => Classical.epsilon_spec (hu τ)
  have hk : emb M (kUnit M) = PiTensorProduct.tprod ℂ v := PiTensorProduct.map_tprod _ _
  rw [hk, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod, (ipM_spec M μ 𝓕 T U h v v).2]
  simp [inner_self_eq_norm_sq_to_K, hv]

theorem emb_eq_zero {τ : D.what₂.Tau} (h : lowT M τ = ⊥) : emb M = 0 := by
  classical
  ext v
  have : (lowT M τ).subtype (v τ) = 0 := (Submodule.mem_bot ℂ).1 (h ▸ (v τ).2)
  simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.zero_apply]
  exact MultilinearMap.map_coord_zero _ τ this

theorem integral_zero_right (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T U : MMap M) (hU : U = 0) (k : SmT M) :
    ipM M μ 𝓕 T U = ∫ g in 𝓕, star (PiTensorProduct.lift T k g) * PiTensorProduct.lift U k g ∂μ := by
  subst hU
  choose s hs using GlobalTheory.Mem.EasyInputs.smAll D V S M
  have hs0 : ∏ τ, ⟪(s τ : M.H τ), (s τ : M.H τ)⟫_ℂ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => inner_self_ne_zero.2 fun h => hs τ (Submodule.coe_eq_zero.1 h)
  have hz : IsMultIP M μ 𝓕 T 0 0 := by
    intro v v'; simp
  rw [hasPeterssonInner_unique _ _ _ _ _ s hs0 (ipM_spec _ _ _ _ _ ⟨_, hz⟩) hz]
  simp

end Unit

theorem lift_post {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (L : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (U : MMap M) :
    PiTensorProduct.lift (postOn M L U) = L ∘ₗ PiTensorProduct.lift U := by
  ext v
  simp [postOn]

section Row

variable {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)

set_option maxHeartbeats 1000000 in

theorem ipM_theta {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (x : D.what₂.Mt μ (j.1 + 1)) (y : D.what₂.Mj (j.1 + 1))
    (T T' : MMap (X.R.MW j (sg0 D X.A))) (hT : PiTensorProduct.lift T = (X.IL.jMj j y).1)
    (hT' : PiTensorProduct.lift T' = (X.IL.jMj j (D.what₂.thetaP μ (j.1 + 1) x)).1) :
    ipM (X.R.MW j (sg0 D X.A)) (X.R.νW j) (X.R.fdW j) T T' =
      ∫ g in X.R.fdW j, star (PiTensorProduct.lift T (emb _ (kUnit (X.R.MW j (sg0 D X.A)))) g) *
        (∫ h in X.R.fdV j (X.tupT μ), thetaKO (X.R.ωP j (X.tupT μ)) h g
          (X.R.ptP j (X.tupT μ) (X.R.ioP j (kUnit (X.R.MW j (sg0 D X.A))) (X.fn hμ j x h))) ∂(X.R.νV j (X.tupT μ)))
        ∂(X.R.νW j) := by
  have hM := X.given.core.models
  obtain ⟨w, hw1, hw2, hw3⟩ := X.fire.2.1 μ hμ j x
  have hth := X.recR.tied.lift.theta μ hμ j x w (X.fire.1 _ hμ j) hw1 hw2 hw3
  obtain ⟨U, hU, hUw⟩ := hw1
  have hUw' : PiTensorProduct.lift U = w := hUw
  obtain ⟨T₀, hT₀, hT₀y⟩ := (X.IL.jMj j y).2
  have hTT : T₀ = T := PiTensorProduct.lift.injective (hT₀y.trans hT.symm)
  subst hTT
  obtain ⟨hT1, hT2⟩ := (mem_goodPart _ _ _ _ _ _).1 hT₀
  have hT'U : T' = postOn (X.R.MW j (sg0 D X.A)) (X.R.eWf j (sg0 D X.A)) U := by
    apply PiTensorProduct.lift.injective
    rw [hT', hth, ← hUw']
    exact (lift_post (X.R.MW j (sg0 D X.A)) _ U).symm
  have hin : ∀ g, (∫ h in X.R.fdV j (X.tupT μ), thetaKO (X.R.ωP j (X.tupT μ)) h g
      (X.R.ptP j (X.tupT μ) (X.R.ioP j (kUnit (X.R.MW j (sg0 D X.A))) (X.fn hμ j x h))) ∂(X.R.νV j (X.tupT μ))) =
      PiTensorProduct.lift U (emb _ (kUnit (X.R.MW j (sg0 D X.A)))) g := by
    intro g
    have e1 := (X.fire.1 _ hμ j).eq (X.IL.jMt μ hμ j x) (kUnit (X.R.MW j (sg0 D X.A))) g
    rw [← hw2, ← hUw'] at e1
    exact e1.symm
  obtain ⟨p1, p2⟩ := ipM_proj X.R hM X.given.irr j (mult_le_wall X.R X.F false j hT1) (mult_le_wall X.R X.F false j hU) hT2
  simp only [hin]
  rw [hT'U]
  refine p1.trans ?_
  by_cases hne : ∀ τ, lowT (X.R.MW j (sg0 D X.A)) τ ≠ ⊥
  · exact (integral_kUnit _ hne _ _ _ _ p2).symm
  · push Not at hne
    obtain ⟨τ, hτ⟩ := hne
    have h0 := emb_eq_zero _ hτ
    have hw0 : w = 0 := X.fire.2.2 j w ⟨U, hU, hUw⟩
      ((congrArg (fun e => w ∘ₗ e) h0).trans (LinearMap.comp_zero _))
    have hU0 : U = 0 := PiTensorProduct.lift.injective (by rw [hUw', hw0, map_zero])
    exact integral_zero_right (X.R.MW j (sg0 D X.A)) _ _ _ _ hU0 _

end Row

section Forms

variable {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} {X : GlobalTheory.NJoin.RealAt D cf nch tp}
  {M : MtFam D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}

theorem ext_pre {V : HSp D} {n : ℕ} (c : CoefA V) (hc : ∀ h ∈ GfC V, c.ρ h = 1) (PV : principalLevelFrame.RowPsi V n)
    (f : Bridge.Gf V → c.W) : c.ext (fun k => c.ext f (PV.ψ (preF PV k))) = c.ext f := by
  refine congrArg c.ext (funext fun k => ?_)
  have hex : ∃ κ, (finHom V).rangeRestrict (PV.ψ κ) = k := by
    obtain ⟨κ, hκ, e⟩ := Formalism.IndefR.Eqv.Act.exists_finLift V k
    obtain ⟨h, rfl⟩ := PV.onto κ hκ
    exact ⟨h, Subtype.ext e⟩
  have hp : (finHom V).rangeRestrict (PV.ψ (preF PV k)) = k := by
    unfold preF
    rw [dif_pos hex]
    exact hex.choose_spec
  show c.ρ (PV.ψ (preF PV k))⁻¹ (f ((finHom V).rangeRestrict (PV.ψ (preF PV k)))) = _
  rw [hp, hc _ (inv_mem (PV.into _)), Module.End.one_apply]

set_option maxHeartbeats 1000000 in

theorem ext_real (hV : X.R.models_cV) (A : GlobalTheory.NJoin.Agree X M rep) {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m)
    (x : D.what₂.Mt μ (j.1 + 1)) :
    (X.R.cV j).ext (fun k => (A.eW μ hμ j).symm ((M μ (j.1 + 1) (by omega) (by omega)).real x (A.a j * preF (A.PV j) k))) =
      X.fn hμ j x := by
  obtain ⟨z, hz⟩ : X.fn hμ j x ∈ LinearMap.range (X.R.extV j (X.tupT μ)) := (X.IL.jMt μ hμ j x).2.1
  have hz' : (X.R.cV j).ext ((X.R.HV j (X.tupT μ)).e z) = X.fn hμ j x := hz
  have e : (fun k => (A.eW μ hμ j).symm ((M μ (j.1 + 1) (by omega) (by omega)).real x (A.a j * preF (A.PV j) k))) =
      fun k => X.fn hμ j x ((A.PV j).ψ (preF (A.PV j) k)) := by
    funext k
    refine (LinearEquiv.symm_apply_eq _).2 ((A.real μ hμ j x _).trans ?_)
    rw [inv_mul_cancel_left]
  refine (congrArg (X.R.cV j).ext e).trans ?_
  generalize X.fn hμ j x = φ at hz' ⊢
  subst hz'
  exact ext_pre _ (hV j).1 _ _

theorem ext_real_cast (hV : X.R.models_cV) (A : GlobalTheory.NJoin.Agree X M rep) {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m)
    (k : ℕ) (hk : j.1 + 1 = k) (p1 : 1 ≤ k) (p2 : k ≤ D.R.m) (x : D.what₂.Mt μ k) :
    (X.R.cV j).ext (fun q => (Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (M μ k p1 p2).wt.W) (fun _ _ => A.eW μ hμ j) hk p1 p2).symm
        ((M μ k p1 p2).real x (A.a j * preF (A.PV j) q))) =
      X.fn hμ j (hk.symm ▸ x) := by
  subst hk
  exact ext_real hV A hμ j x

end Forms

section Canon

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {P : Pin hL D} (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp)

set_option maxHeartbeats 1000000 in

theorem inner_theta {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (k : ℕ) (hk : j.1 + 1 = k) (Y : RowMod D P.rep k)
    (hc : GlobalTheory.NJoin.IsCanon X j hk Y) (x : D.what₂.Mt μ k) (y : D.what₂.Mj k) :
    inner ℂ y (D.what₂.thetaP μ k x) = (cC hc : ℂ) *
      ∫ g in X.R.fdW j, star (yv hc ⟨Y.φ y, Y.φ_mem y⟩ g) *
        (∫ h in X.R.fdV j (X.tupT μ), thetaKO (X.R.ωP j (X.tupT μ)) h g
          (phi0 j (X.tupT μ) (X.fn hμ j (hk.symm ▸ x) h)) ∂(X.R.νV j (X.tupT μ))) ∂(X.R.νW j) := by
  subst hk
  obtain ⟨-, -, -, -, hB, hφ⟩ := Classical.choose_spec (Classical.choose_spec hc)
  refine (Y.φ_inner _ _).trans ((hB _ (Y.φ_mem _) _ (Y.φ_mem _)).trans (congrArg (fun z => (cC hc : ℂ) * z) ?_))
  exact ipM_theta X hμ j x y (eC hc (Y.φ y)) (eC hc (Y.φ (D.what₂.thetaP μ (j.1 + 1) x))) (hφ y) (hφ _)

end Canon

theorem main : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)) (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (x : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) (y : D.what₂.Mj (D.nd.j i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)), (F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) = (P.M.loc i).real x → inner ℂ y (D.what₂.thetaP (D.nd.mu i) (D.nd.j i) x) = GlobalTheory.ThetaTri.lamI A i j hj hc hμ (GlobalTheory.ThetaTri.phi0 j (X.tupT (D.nd.mu i))) F ⟨Y.φ y, Y.φ_mem y⟩ := by
  intro hL D P X A i j hj Y hc hμ x y F hF
  have hf : fV A i j hj hμ F = X.fn hμ j (hj.symm ▸ x) := by
    refine Eq.trans ?_ (ext_real_cast X.given.core.models.cV A hμ j _ hj (D.nd.j_range i).1 (D.nd.j_range i).2 x)
    show (X.R.cV j).ext (fun k => (eWloc A i j hj hμ).symm
      ((F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) (A.a j * preF (A.PV j) k))) = _
    rw [hF]
    rfl
  rw [inner_theta X hμ j _ hj Y hc x y, ← hf]
  rfl

end GlobalTheory.ThetaRead

end
