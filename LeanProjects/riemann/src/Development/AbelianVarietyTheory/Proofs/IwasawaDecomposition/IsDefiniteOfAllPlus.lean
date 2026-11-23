import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplicitySpaceDefiniteContinuousInvariantEqui
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteSmoothIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorProductDefiniteUnitaryLocalModelsIrreducib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.DefLift GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DefiniteMult

section DefiniteBasics

open Matrix MeasureTheory
open scoped ComplexOrder

theorem sig_eq_of_posDef {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) {p q : ℕ}
    (h : Formalism.UG.HasSignature G p q) : (p, q) = (n, 0) := by
  obtain ⟨hn, Q, hQ⟩ := Formalism.UG.P.sig_data G p q h
  have hq : q = 0 := by
    by_contra hq
    have j : Fin q := ⟨0, Nat.pos_of_ne_zero hq⟩
    have h1 := (hG.posSemidef.conjTranspose_mul_mul_same Q).diag_nonneg (i := Sum.inr j)
    rw [hQ] at h1
    simp [Formalism.UG.Jpq] at h1
    exact absurd h1 (by norm_num)
  subst hq
  simp at hn
  rw [hn]

theorem exists_tauE_or_conj (D : D7) (σ : D.host.E →+* ℂ) :
    ∃ τ, σ = tauE D τ ∨ σ = (starRingEnd ℂ).comp (tauE D τ) := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 σ
  have key : ∀ (t : D.R.GG) (ht : t ∈ D.R.Psi),
      tauE D (D.eTau.symm ⟨t, ht⟩) = D.host.emb t := fun t ht => by
    unfold tauE
    rw [Equiv.apply_symm_apply]
  by_cases h : g ∈ D.R.Psi
  · exact ⟨D.eTau.symm ⟨_, h⟩, Or.inl (key g h).symm⟩
  · have h' : g * D.R.cc ∈ D.R.Psi := by
      by_contra h2
      exact h ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).2 h2)
    refine ⟨D.eTau.symm ⟨_, h'⟩, Or.inr ?_⟩
    rw [key, Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    have := D.host.conjE_apply (D.host.emb g) x
    exact ((starRingEnd_self_apply _).symm.trans (congrArg (starRingEnd ℂ) this.symm))

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem isDefinite_of_allPlus (hs : V.SigOK) (h : AllPlus M) : V.IsDefinite := by
  intro σ
  refine Or.inl (sig_eq_of_posDef ?_ (hs σ))
  obtain ⟨τ, rfl | rfl⟩ := exists_tauE_or_conj D σ
  · exact h.posDef τ
  · have e : V.gram.map ((starRingEnd ℂ).comp (tauE D τ)) = (gramAt D V τ)ᴴᵀ := by
      ext i j
      rfl
    rw [e]
    exact (h.posDef τ).conjTranspose.transpose

theorem rTr_mem_of_places {θ : InfFam D} (hθ : IsInfFam θ) (U : Set (GA D V → ℂ))
    (hU : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ f ∈ U, rTr V (atTau θ V τ g) f ∈ U) {k : GA D V}
    (hk : k ∈ GinfC V) : ∀ f ∈ U, rTr V k f ∈ U := by
  classical
  obtain ⟨-, -, r3, -⟩ := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hu := GlobalTheory.RealLift.archM_mem hθ V k
  have e : GlobalTheory.RealLift.prodAt θ V Finset.univ.toList (fun τ => Formalism.L2.Pj.archM V (θ τ) k) = k :=
    r3 _ (GlobalTheory.RealLift.prodAt_mem θ V _ _) _ hk fun τ => by
      rw [GlobalTheory.RealLift.infMat_prodAt hθ V hu τ _ (Finset.nodup_toList _),
        if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]
      rfl
  rw [← e]
  clear e
  generalize (Finset.univ.toList : List D.what₂.Tau) = l
  induction l with
  | nil =>
    intro f hf
    convert hf using 1
    funext g
    exact congrArg f (mul_one g)
  | cons τ l ih =>
    intro f hf
    convert hU τ _ (hu τ) _ (ih f hf) using 1
    funext g
    exact congrArg f (mul_assoc _ _ _).symm

open Classical in
theorem inclT_update_tprod (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    inclT M (PiTensorProduct.tprod ℂ (Function.update v τ w)) = actT M τ g (inclT M (PiTensorProduct.tprod ℂ v)) := by
  unfold inclT actT
  simp only [PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  by_cases c : ρ = τ
  · subst c
    simpa using hw
  · simp [Function.update_of_ne c]

end DefiniteBasics

theorem exists_descend {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (p : G →* H)
    (ρ : G →* Module.End ℂ W) (Ψ : G → W) (hU : ∀ a ∈ p.ker, ∀ h, Ψ (h * a) = ρ a⁻¹ (Ψ h)) :
    ∃ f : p.range → W, ∀ h, f (p.rangeRestrict h) = ρ h (Ψ h) := by
  refine ⟨fun q => ρ q.2.choose (Ψ q.2.choose), fun h => ?_⟩
  have ha : h⁻¹ * (p.rangeRestrict h).2.choose ∈ p.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, (p.rangeRestrict h).2.choose_spec]
    exact inv_mul_cancel _
  have := hU _ ha h
  rw [mul_inv_cancel_left] at this
  beta_reduce
  rw [this, ← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_inv, mul_inv_cancel_left]

theorem rho_right {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (ρ : G →* Module.End ℂ W) (g : G) {k : G}
    (hk : ρ k = 1) : ρ (g * k) = ρ g := by
  rw [map_mul, hk, mul_one]

theorem rho_right_inv {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (ρ : G →* Module.End ℂ W) (g : G) {k : G}
    (hk : ρ k⁻¹ = 1) : ρ (g * k)⁻¹ = ρ g⁻¹ := by
  rw [mul_inv_rev, map_mul, hk, one_mul]

theorem adForms_level {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* G}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {f : G → W} (hf : f ∈ Bridge.AdForms ι ρ J χ) (h : G)
    (k : J) : f (h * k) = (χ k : ℂ) • f h := by
  simpa using hf 1 h k

theorem range_ker_mul {G H : Type} [Group G] [Group H] (p : G →* H) {a : G} (ha : a ∈ p.ker) (k : G) :
    p.rangeRestrict (a * k) = p.rangeRestrict k := by
  rw [map_mul, show p.rangeRestrict a = 1 from Subtype.ext ha, one_mul]

theorem mem_adForms {G H W : Type} [Group G] [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (p : G →* H)
    (Γ K : Subgroup G) (hK : ∀ q : p.range, ∃ κ ∈ K, p.rangeRestrict κ = q) (ρ : G →* Module.End ℂ W) (hρ : ∀ κ ∈ K, ρ κ = 1)
    (J : Subgroup p.range) (χ : J →* ℂˣ) (Ψ : G → W) (f : p.range → W) (hf : ∀ h, f (p.rangeRestrict h) = ρ h (Ψ h))
    (h : ∀ γ ∈ Γ, ∀ g, ∀ κ ∈ K, ∀ hκ : p.rangeRestrict κ ∈ J, Ψ (γ * g * κ) = (χ ⟨_, hκ⟩ : ℂ) • Ψ g) :
    f ∈ Bridge.AdForms (p.rangeRestrict.comp Γ.subtype) (ρ.comp Γ.subtype) J χ := by
  rintro γ q ⟨k, hk⟩
  obtain ⟨g, rfl⟩ := p.rangeRestrict_surjective q
  obtain ⟨κ, hκ, rfl⟩ := hK k
  show f (p.rangeRestrict γ * p.rangeRestrict g * p.rangeRestrict κ) = _ • ρ γ _
  rw [← map_mul, ← map_mul, hf, hf, rho_right ρ _ (hρ κ hκ), h γ γ.2 g κ hκ hk, map_smul, map_mul, Module.End.mul_apply]

theorem exists_fin_lift {D : D7} (V : HSp D) (q : Bridge.Gf V) : ∃ κ ∈ GfC V, (finHom V).rangeRestrict κ = q := by
  obtain ⟨κ', rfl⟩ := (finHom V).rangeRestrict_surjective q
  obtain ⟨a, ha, κ, hκ, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 κ'
  exact ⟨κ, hκ, (range_ker_mul (finHom V) ha κ).symm⟩

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {θ : InfFam D} {c : CoefA V}
  {pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ}

theorem real_le (hθ : IsInfFam θ) (U : Submonoid (GA D V))
    (hU : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), atTau θ V τ g ∈ U) {k : GA D V} (hk : k ∈ GinfC V) : k ∈ U := by
  classical
  have h := rTr_mem_of_places hθ {f | ∃ x ∈ U, f = rTr V x (fun g => if g ∈ U then 1 else 0)}
    (fun τ g hg f hf => by
      obtain ⟨x, hx, rfl⟩ := hf
      exact ⟨_, U.mul_mem (hU τ g hg) hx, funext fun y => by simp only [rTr, mul_assoc]⟩) hk _ ⟨1, U.one_mem, rfl⟩
  obtain ⟨x, hx, e⟩ := h
  have := congrFun e 1
  simp only [rTr, mul_one, one_mul, if_pos hx] at this
  by_contra hn
  rw [if_neg hn] at this
  exact zero_ne_one this

theorem ext_injective (c : CoefA V) : Function.Injective c.ext := by
  intro f f' h
  funext q
  obtain ⟨_, g, rfl⟩ := q
  have := congrArg (c.ρ g) (congrFun h g)
  exact (GlobalTheory.DefiniteEnd.rho_inv_cancel g _).symm.trans (this.trans (GlobalTheory.DefiniteEnd.rho_inv_cancel g _))

theorem pair_tens (hp : AllPlus M) (hsm : ∀ τ, M.sm τ = ⊤) (hinj : Function.Injective (inclT M)) {π} (hπ : IsTensAct M π)
    (hpr : IsDualPair θ M c pr) (τ : D.what₂.Tau) (u : Matrix.unitaryGroup (Fin V.rank) ℂ) (w : c.W) (x : SmT M) :
    pr w (π τ u x) = pr (c.ρ (atTau θ V τ (unfr M τ u))⁻¹ w) x := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    let y : M.sm τ := ⟨M.rep τ (unfr M τ u) (v τ), Submodule.eq_top_iff'.1 (hsm τ) _⟩
    have e : π τ u (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ y) :=
      hinj ((hπ τ u _).trans (inclT_update_tprod τ _ v y rfl).symm)
    have := hpr.2 τ _ (hp.unfr_mem τ u) (c.ρ (atTau θ V τ (unfr M τ u))⁻¹ w) v y rfl
    rw [GlobalTheory.DefiniteEnd.rho_inv_cancel] at this
    rw [map_smul, map_smul, map_smul, e, this]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem pair_bijective (hθ : IsInfFam θ) (hp : AllPlus M) (hc : c.Is) (hpr : IsDualPair θ M c pr) :
    Function.Bijective pr := by
  have m := AllPlus.finite_smooth_irreducible D V S M hp
  obtain ⟨fd, inj, π, hπ, irr⟩ := tensor_irreducible D V S M m hp
  have key := pair_tens hp (fun τ => (m τ).2.1) inj hπ hpr
  constructor
  · let U : Submonoid (GA D V) :=
      { carrier := {h | ∀ w, pr w = 0 → pr (c.ρ h⁻¹ w) = 0}
        one_mem' := fun w hw => by rwa [inv_one, map_one]
        mul_mem' := fun {a b} ha hb w hw => by
          rw [mul_inv_rev, map_mul]
          exact hb _ (ha w hw) }
    have hU : ∀ h, h ∈ U := fun h => by
      obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h
      refine U.mul_mem (real_le hθ U (fun τ g hg w hw => ?_) ha) fun w hw => by rwa [hc.1 _ (inv_mem hk)]
      obtain ⟨u, rfl⟩ := hp.exists_unfr τ hg
      refine LinearMap.ext fun x => ?_
      rw [← key, hw]; rfl
    rw [← LinearMap.ker_eq_bot]
    refine (hc.2.2.2.2 _ fun h => ?_).resolve_right fun e => hpr.1 (LinearMap.ker_eq_top.1 e)
    rintro _ ⟨w, hw, rfl⟩
    have := hU h⁻¹ w hw
    rwa [inv_inv] at this
  · have h : Function.Injective pr.flip := by
      rw [← LinearMap.ker_eq_bot]
      refine (irr _ fun τ u x hx => ?_).resolve_right fun e => hpr.1 ?_
      · exact LinearMap.ext fun w => (key τ u w x).trans (LinearMap.congr_fun hx _)
      · exact LinearMap.ext₂ fun w x => LinearMap.congr_fun₂ (LinearMap.ker_eq_top.1 e) x w
    exact LinearMap.flip_injective_iff₂.1 h

theorem toMap_injective (hθ : IsInfFam θ) (hp : AllPlus M) (hc : c.Is) (hpr : IsDualPair θ M c pr) :
    Function.Injective (c.toMap pr) := fun _ _ h =>
  ext_injective c (funext fun g => (pair_bijective hθ hp hc hpr).1
    (LinearMap.ext fun v => congrFun (LinearMap.congr_fun h v) g))

variable {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem toMap_mem (hθ : IsInfFam θ) (hs : V.SigOK) (hp : AllPlus M) (hc : c.Is) (hpr : IsDualPair θ M c pr)
    {f : Bridge.Gf V → c.W} (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ) :
    c.toMap pr f ∈ MultT θ M (levS V β (flag1L L)) (levChi V β (flag1L L)) := by
  have h := GlobalTheory.DefiniteEnd.isMultMap_toMap hθ hs (isDefinite_of_allPlus hs hp) M hc hpr hf
  refine (mem_multT θ M _ _ _).2 (Submodule.subset_span ⟨h.aut, h.cusp, fun v k hk g => ?_, h.equiv, h.cont⟩)
  have e : f ((finHom V).rangeRestrict (g * k)) = levChi V β (flag1L L) k • f ((finHom V).rangeRestrict g) :=
    (congrArg f (map_mul (finHom V).rangeRestrict g k)).trans (adForms_level hf _ ⟨(finHom V).rangeRestrict k, hk.2⟩)
  have e2 : c.ext f (g * k) = levChi V β (flag1L L) k • c.ext f g :=
    ((congrArg (c.ρ (g * k)⁻¹) e).trans (LinearMap.congr_fun (rho_right_inv c.ρ g (hc.1 _ (inv_mem hk.1))) _)).trans
      (map_smul _ _ _)
  exact (congrArg (fun w => pr w (PiTensorProduct.tprod ℂ v)) e2).trans (LinearMap.congr_fun (map_smul pr _ _) _)

theorem exists_form (hθ : IsInfFam θ) (hp : AllPlus M) (hc : c.Is) (hpr : IsDualPair θ M c pr)
    {T : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hT : T ∈ MultT θ M (levS V β (flag1L L)) (levChi V β (flag1L L))) :
    ∃ f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ, c.toMap pr f = T := by
  have m := AllPlus.finite_smooth_irreducible D V S M hp
  obtain ⟨fd, inj, π, hπ, irr⟩ := tensor_irreducible D V S M m hp
  have key := pair_tens hp (fun τ => (m τ).2.1) inj hπ hpr
  have hb := pair_bijective hθ hp hc hpr
  have hE := GlobalTheory.multT_cont_left_equiv D θ V S M π _ _ hp (fun τ => (m τ).2.1) inj hπ T hT
  choose Ψ hΨ using fun h : GA D V => hb.2 (LinearMap.proj h ∘ₗ T)
  replace hΨ : ∀ h x, pr (Ψ h) x = T x h := fun h x => LinearMap.congr_fun (hΨ h) x
  have hlev : ∀ k ∈ levS V β (flag1L L), ∀ x g, T x (g * k) = levChi V β (flag1L L) k * T x g := fun k hk x g => by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := (mult_value_left_cont_level θ M _ _ _ ((mem_multT θ M _ _ _).1 hT) v).2.2 k hk g
      rw [map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]
      exact congrArg (r * ·) this
    | add x y hx hy => rw [map_add, Pi.add_apply, Pi.add_apply, hx, hy, mul_add]
  let U : Submonoid (GA D V) :=
    { carrier := {a | ∀ h, Ψ (h * a) = c.ρ a⁻¹ (Ψ h)}
      one_mem' := fun h => by rw [mul_one, inv_one, map_one]; rfl
      mul_mem' := fun {a b} ha hb h => by rw [← mul_assoc, hb, ha, mul_inv_rev, map_mul]; rfl }
  obtain ⟨f, hf⟩ := exists_descend (finHom V) c.ρ Ψ fun a ha => real_le hθ U (fun τ g hg h => by
      obtain ⟨u, rfl⟩ := hp.exists_unfr τ hg
      refine hb.1 (LinearMap.ext fun x => ?_)
      rw [← key, hΨ, hΨ, (hE x).2.2]; rfl) ha
  refine ⟨f, mem_adForms (finHom V) (GQ V) (GfC V) (exists_fin_lift V) c.ρ hc.1 _ _ Ψ f hf fun γ hγ g κ hκ hk => ?_,
    LinearMap.ext fun x => funext fun h => ?_⟩
  · have e2 : Ψ (γ * g * κ) = levChi V β (flag1L L) κ • Ψ g := by
      refine hb.1 (LinearMap.ext fun x => ?_)
      rw [map_smul, LinearMap.smul_apply, hΨ, hΨ, hlev κ ⟨hκ, hk⟩, (hE x).2.1 γ hγ, smul_eq_mul]
    exact e2
  · have e := GlobalTheory.DefiniteEnd.rho_inv_cancel (c := c) h⁻¹ (Ψ h)
    rw [inv_inv] at e
    exact (congrArg (fun w => pr w x) ((congrArg (c.ρ h⁻¹) (hf h)).trans e)).trans (hΨ h x)

theorem map_adForms (hθ : IsInfFam θ) (hs : V.SigOK) (hp : AllPlus M) (hc : c.Is) (hpr : IsDualPair θ M c pr) :
    (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ).map (c.toMap pr) =
      MultT θ M (levS V β (flag1L L)) (levChi V β (flag1L L)) :=
  le_antisymm (by rintro _ ⟨f, hf, rfl⟩; exact toMap_mem hθ hs hp hc hpr hf) fun _ hT => exists_form hθ hp hc hpr hT

theorem allPlus_parB (P : TPar D) {j : ℕ} (hj : D.R.m - 1 ≤ j) (M : DSModel V (parB P j)) : AllPlus M := by
  intro τ a
  obtain ⟨-, q, -, hq⟩ := M.enum τ
  have h : (q a, M.ε τ a) ∈ parB P j τ := hq ▸ Finset.mem_image_of_mem _ (Finset.mem_univ a)
  simp only [parB, dualPar, TPar.Dpar, Finset.mem_image, Finset.mem_union, Finset.mem_biUnion, Prod.mk.injEq] at h
  obtain ⟨_, ⟨x, hx, rfl⟩, -, h⟩ := h
  rw [← h]
  rcases hx with (⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | ⟨i, -, y, -, rfl⟩
  · rfl
  · exact decide_eq_true (Or.inl (by have := i.2; omega))
  · rfl

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem range_top (hθ : R.models_inf) (hc : R.models_cX) (hpr : R.models_prX) (hH : R.models_HX) (t : T) :
    LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) =
      MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t)) := by
  have e : flag1L (R.datXt t) = R.datXt t := rfl
  have h := map_adForms (β := R.βX) (L := R.datXt t) hθ D.sp.X'_sig (allPlus_parB _ (Nat.sub_le _ _) _) hc hpr
  rw [e] at h
  exact (LinearMap.range_comp _ _).trans ((congrArg (Submodule.map _) (hH t).2.1).trans h)

theorem top_injective (hθ : R.models_inf) (hc : R.models_cX) (hpr : R.models_prX) (hH : R.models_HX) (t : T) :
    Function.Injective (R.cX.toMap R.prX ∘ₗ (R.HX t).e) :=
  (toMap_injective hθ (allPlus_parB _ (Nat.sub_le _ _) _) hc hpr).comp (hH t).1

theorem extV_injective (hH : R.models_HV) (i : Fin D.R.m) (t : T) : Function.Injective (R.extV i t) :=
  (ext_injective (R.cV i)).comp (hH i t).1

end Real

end GlobalTheory.DefiniteMult

end
