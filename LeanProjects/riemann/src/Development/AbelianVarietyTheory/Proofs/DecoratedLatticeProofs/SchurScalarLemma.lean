import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoefficientVectorReadingRealRepresentation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefDualPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary

noncomputable section

namespace GlobalTheory.TopVal.Scalar

section Alg

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms Matrix GlobalTheory.CoefSpace

theorem schur {G W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] (ρ : G → Module.End ℂ W)
    (hirr : ∀ U : Submodule ℂ W, (∀ h, U.map (ρ h) ≤ U) → U = ⊥ ∨ U = ⊤) (T : Module.End ℂ W)
    (hT : ∀ h w, T (ρ h w) = ρ h (T w)) : ∃ a : ℂ, ∀ w, T w = a • w := by
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue T
  refine ⟨a, fun w => ?_⟩
  have h := (hirr (T.eigenspace a) fun h => ?_).resolve_left ha
  · exact Module.End.mem_eigenspace_iff.1 (h ▸ Submodule.mem_top)
  · rintro _ ⟨x, hx, rfl⟩
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [hT, Module.End.mem_eigenspace_iff.1 hx, map_smul]

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem exists_ext {K W : Type} [Field K] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (lam : ι → DomWeight n)
    (c : VV K lam →ₛₗ[σ] W) : ∃ c' : VV ℂ lam →ₗ[ℂ] W, ∀ w, c' (bcVV σ lam w) = c w := by
  let b := Module.Basis.mk (bcVV_indep σ lam) (bcVV_span σ lam).ge
  refine ⟨b.constr ℂ fun i => c (bVV K lam i), fun w => ?_⟩
  rw [← (bVV K lam).sum_repr w, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : bcVV σ lam (bVV K lam i) = b i := (Module.Basis.mk_apply (bcVV_indep σ lam) (bcVV_span σ lam).ge i).symm
  rw [map_smulₛₗ (bcVV σ lam), map_smul, e, Module.Basis.constr_basis, map_smulₛₗ c]

theorem ext_bc {K W : Type} [Field K] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (lam : ι → DomWeight n)
    {f g : VV ℂ lam →ₗ[ℂ] W} (h : ∀ w, f (bcVV σ lam w) = g (bcVV σ lam w)) : f = g :=
  LinearMap.ext_on_range (bcVV_span σ lam) fun _ => h _

theorem fnOf_actP (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) (P : Pol ℂ ι n)
    (y y' : Frames G) (h : ∀ τ, y'.1 τ = (g τ : Matrix (Fin n) (Fin n) ℂ)ᵀ * y.1 τ) :
    fnOf G (shiftOf lam) 1 (actP lam g P) y = fnOf G (shiftOf lam) 1 P y' := by
  have e := Formalism.L2.Col.evFr_actP G (RingHom.id ℂ) lam g P
  rw [Formalism.L2.Col.evFr_eq_fnOf] at e
  simp only [MvPolynomial.map_id] at e
  rw [e]
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul, h]
  rfl

theorem exists_equiv (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n)
    {V : Type} [AddCommGroup V] [Module ℂ V] (j : V →ₗ[ℂ] (Frames G → ℂ))
    (hinj : Function.Injective j) (hr : LinearMap.range j = ValC G lam) :
    ∃ φ : V ≃ₗ[ℂ] VV ℂ lam, ∀ v, j v = fnOf G (shiftOf lam) 1 (φ v).1 := by
  have hf : Function.Injective (fnOf G (shiftOf lam) 1) :=
    Formalism.L2.Col.fnOf_injective G _ 1 (fun τ => by simp) ⟨fun _ => 1, fun τ => by simp⟩
  have hr' : LinearMap.range j = (VV ℂ lam).map (fnOf G (shiftOf lam) 1) := by
    rw [hr, ValC, GlobalTheory.Pdv.FormsStd.cSpan_eq_VV]
  refine ⟨(LinearEquiv.ofInjective j hinj).trans ((LinearEquiv.ofEq _ _ hr').trans
    (Submodule.equivMapOfInjective _ hf (VV ℂ lam)).symm), fun v => ?_⟩
  exact (congrArg Subtype.val ((Submodule.equivMapOfInjective _ hf (VV ℂ lam)).apply_symm_apply
    (LinearEquiv.ofEq _ _ hr' (LinearEquiv.ofInjective j hinj v)))).symm

end Alg

section Group

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Forms Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.DefLift GlobalTheory.CoefSpace GlobalTheory.DefiniteMult Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {θ : InfFam D} {c : CoefA V}
  {pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ}

theorem infGL_fin {h : GA D V} (hh : h ∈ GfC V) : infGL θ V h = 1 := by
  have h1 : infHom V h = 1 := hh
  rw [infGL, MonoidHom.comp_apply, h1, map_one]

theorem eqv_real (hθ : IsInfFam θ) (hc : c.Is) (lam : D.what₂.Tau → DomWeight V.rank) (f : VV ℂ lam →ₗ[ℂ] c.W)
    (hf : ∀ γ ∈ GQ V, ∀ x, f (rhoK lam (infGL θ V γ) x) = c.ρ γ (f x)) {u : GA D V} (hu : u ∈ GinfC V) (x : VV ℂ lam) :
    f (rhoK lam (infGL θ V u) x) = c.ρ u (f x) := by
  by_contra hne
  have h0 : ∀ f' : (coefA θ V lam 1).W →ₗ[ℂ] c.W, Continuous f' := fun f' => f'.continuous_of_finiteDimensional
  have h1 : Continuous fun h : GA D V => f (rhoK lam (infGL θ V h) x) := (h0 f).comp (coefA_cont lam 1 hθ x)
  obtain ⟨γ, hγ, k, hk, hU, -⟩ := GlobalTheory.RealApprox.weak_approx_real V u hu _ (isOpen_ne_fun h1 (hc.2.2.1 (f x))) hne
  refine hU ?_
  rw [map_mul, infGL_fin hk, mul_one, map_mul, hc.1 k hk, mul_one]
  exact hf γ hγ x

theorem infGL_rat (hθ : IsInfFam θ) {K : Type} [Field K] (σ : K →+* ℂ) (emb : D.what₂.Tau → D.host.E →+* K)
    (hemb : ∀ τ x, σ (emb τ x) = tauE D τ x) (γ : GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE) :
    infGL θ V γ = fun τ => Formalism.UG.bc σ (embGL emb γE τ) := by
  funext τ
  refine Units.ext (Matrix.ext fun a b => ?_)
  have h1 : ((matHom V (γ : GA D V)).1 a b) = incA D (γE.1 a b) := by
    rw [show matHom V (γ : GA D V) = _ from hγ]
    rfl
  show θ τ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    ((matHom V (γ : GA D V)).1 a b)) = σ (emb τ (γE.1 a b))
  rw [h1, hemb, ← (hθ τ).1]
  exact congrArg (θ τ) ((Algebra.TensorProduct.map_tmul _ _ _ _).trans (by rw [map_one]; rfl))

open Classical in

theorem eqv_transpose (hθ : IsInfFam θ) (hp : AllPlus M) (hc : c.Is) (hpr : IsDualPair θ M c pr)
    (lam : D.what₂.Tau → DomWeight V.rank) (φ : SmT M →ₗ[ℂ] VV ℂ lam)
    (hφ : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) →
      (φ (PiTensorProduct.tprod ℂ (Function.update v τ w))).1 =
        actP lam (invTrK (infGL θ V (atTau θ V τ g))) (φ (PiTensorProduct.tprod ℂ v)).1)
    (f : VV ℂ lam →ₗ[ℂ] c.W) (hf : ∀ w v, pr (f w) v = pairBK lam (φ v) w) {u : GA D V} (hu : u ∈ GinfC V) (x : VV ℂ lam) :
    f (rhoK lam (infGL θ V u) x) = c.ρ u (f x) := by
  have m := AllPlus.finite_smooth_irreducible D V S M hp
  let U : Submonoid (GA D V) :=
    { carrier := {h | ∀ x, f (rhoK lam (infGL θ V h⁻¹) x) = c.ρ h⁻¹ (f x)}
      one_mem' := fun x => by rw [inv_one, map_one, map_one, map_one]; rfl
      mul_mem' := fun {a b} ha hb x => by
        rw [_root_.mul_inv_rev, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb, ha] }
  have key := real_le hθ U (fun τ g hg x => ?_) (inv_mem hu) x
  · rwa [inv_inv] at key
  refine (pair_bijective hθ hp hc hpr).1 (PiTensorProduct.ext (MultilinearMap.ext fun v => ?_))
  let y : M.sm τ := ⟨M.rep τ g (v τ), Submodule.eq_top_iff'.1 (m τ).2.1 _⟩
  have h1 := hpr.2 τ g hg (c.ρ (atTau θ V τ g)⁻¹ (f x)) v y rfl
  rw [GlobalTheory.DefiniteEnd.rho_inv_cancel] at h1
  show pr _ (PiTensorProduct.tprod ℂ v) = pr _ (PiTensorProduct.tprod ℂ v)
  rw [← h1, hf, hf, pairBK_apply, pairBK_apply, hφ τ g hg v y rfl,
    ← pairingBInvariantK_holds ℂ _ _ lam (infGL θ V (atTau θ V τ g)), ← rhoK_coe lam (infGL θ V (atTau θ V τ g)), rhoK_mul, ← map_mul,
    mul_inv_cancel, map_one, rhoK_one]

open Classical in

theorem exists_scalar (hθ : IsInfFam θ) (hp : AllPlus M) (hc : c.Is) (hpr : IsDualPair θ M c pr) {n : ℕ} (hn : V.rank = n)
    (lam : D.what₂.Tau → DomWeight n) {K : Type} [Field K] (σ : K →+* ℂ) (emb : D.what₂.Tau → D.host.E →+* K)
    (hemb : ∀ τ x, σ (emb τ x) = tauE D τ x) (cv : VV K lam →ₛₗ[σ] c.W)
    (hcv : ∀ (γ : GQ V) γE (g : GL (Fin n) D.host.E), Bridge.IsRatMat V γ γE → GlobalTheory.Mem.R3.MatEq γE g →
      ∀ v, cv (rhoV emb lam g v) = c.ρ γ.1 (cv v)) (h0 : cv ≠ 0)
    (G G' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (o : Frames G') (ho : (fun τ => (o.1 τ)⁻¹) = 1)
    (j : SmT M →ₗ[ℂ] (Frames G → ℂ)) (hinj : Function.Injective j) (hr : LinearMap.range j = ValC G lam)
    (heqv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) →
      ∀ y y' : Frames G, IsTr (Function.update (fun _ => 1) τ (g.reindex (finCongr hn) (finCongr hn))) y' y →
        j (PiTensorProduct.tprod ℂ (Function.update v τ w)) y = j (PiTensorProduct.tprod ℂ v) y') :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ w v, pr (cv w) v =
      a * pairB lam (Formalism.L2.Col.polOf G' (shiftOf lam) o (j v)) (MvPolynomial.map σ w.1) := by
  subst hn
  obtain ⟨φ, hφ⟩ := exists_equiv G lam j hinj hr
  have hf : Function.Injective (fnOf G (shiftOf lam) 1) :=
    Formalism.L2.Col.fnOf_injective G _ 1 (fun τ => by simp) ⟨fun _ => 1, fun τ => by simp⟩
  have hpol : ∀ v, Formalism.L2.Col.polOf G' (shiftOf lam) o (j v) = (φ v).1 := fun v => by
    have h := Formalism.L2.Col.polOf_fnOf G' (shiftOf lam) o (φ v).1
    rw [ho] at h
    rw [hφ]
    exact h
  haveI : FiniteDimensional ℂ (VV ℂ lam) := Module.Finite.of_basis (bVV ℂ lam)
  have hB : (pairBK (K := ℂ) lam).flip.Nondegenerate := LinearMap.flip_nondegenerate.mpr (pairingBNondegenerate_holds ℂ _ _ lam)
  let e := LinearEquiv.ofBijective pr (pair_bijective hθ hp hc hpr)
  let f : VV ℂ lam ≃ₗ[ℂ] c.W := (LinearMap.BilinForm.toDual _ hB).trans (φ.dualMap.trans e.symm)
  have hfp : ∀ w v, pr (f w) v = pairBK lam (φ v) w := fun w v =>
    LinearMap.congr_fun (e.apply_symm_apply (φ.dualMap (LinearMap.BilinForm.toDual _ hB w))) v
  have h2 : ∀ u ∈ GinfC V, ∀ x, f (rhoK lam (infGL θ V u) x) = c.ρ u (f x) := fun u hu x => by
    refine eqv_transpose hθ hp hc hpr lam φ.toLinearMap (fun τ g hg v w hw => hf (funext fun y => ?_)) f.toLinearMap hfp hu x
    have ha : IsAtTau θ V τ g (atTau θ V τ g) := by
      have hex := (GlobalTheory.PointAtPlace.existsUnique_isAtTau V τ θ hθ g hg).exists
      rw [atTau, dif_pos hex]
      exact hex.choose_spec
    set A := infGL θ V (atTau θ V τ g) with hA
    let y' : Frames G := ⟨fun ρ => ((A ρ)⁻¹ : GL (Fin V.rank) ℂ).1 * y.1 ρ, fun ρ => by
      rw [Matrix.det_mul]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).mul (y.2 ρ)⟩
    rw [fnOf_actP G lam _ _ y y' fun ρ => by rw [invTrK_coe, Matrix.transpose_transpose]]
    have := heqv τ g hg v w hw y y' fun ρ => by
      have e1 : Function.update (fun _ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) τ
          (g.reindex (finCongr rfl) (finCongr rfl)) ρ = (A ρ).1 := by
        by_cases hρ : ρ = τ
        · subst hρ
          rw [Function.update_self]
          exact ha.2.1.symm
        · rw [Function.update_of_ne hρ]
          exact (ha.2.2 ρ hρ).symm
      rw [e1]
      show y.1 ρ = (A ρ).1 * (((A ρ)⁻¹ : GL (Fin V.rank) ℂ).1 * y.1 ρ)
      rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [hφ, hφ] at this
    exact this
  obtain ⟨c', hc'⟩ := exists_ext σ lam cv
  have h1 : ∀ u ∈ GinfC V, ∀ x, c' (rhoK lam (infGL θ V u) x) = c.ρ u (c' x) := fun u hu x => by
    refine eqv_real hθ hc lam c' (fun γ hγ x => ?_) hu x
    obtain ⟨γE, -, hE⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
    have hE' : Bridge.IsRatMat V ⟨γ, hγ⟩ γE := hE.symm
    refine LinearMap.congr_fun (ext_bc σ lam (f := c' ∘ₗ rhoK lam (infGL θ V γ)) (g := c.ρ γ ∘ₗ c') fun w => ?_) x
    have e2 : rhoK lam (infGL θ V γ) (bcVV σ lam w) = bcVV σ lam (rhoV emb lam γE w) := by
      refine Subtype.ext ?_
      show actP lam (infGL θ V γ) (MvPolynomial.map σ w.1) = MvPolynomial.map σ (actP lam (embGL emb γE) w.1)
      rw [GlobalTheory.CoefSpace.map_actP, ← infGL_rat hθ σ emb hemb ⟨γ, hγ⟩ γE hE']
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e2, hc', hc']
    exact hcv ⟨γ, hγ⟩ γE γE hE' ⟨rfl, fun i j i' j' hi hj => by rw [Fin.ext hi, Fin.ext hj]⟩ w
  haveI := hc.2.2.2.1
  obtain ⟨a, ha⟩ := schur (fun h => c.ρ h) hc.2.2.2.2 (c' ∘ₗ f.symm.toLinearMap) fun h w => by
    obtain ⟨u, hu, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h
    obtain ⟨x, rfl⟩ := f.surjective w
    show c' (f.symm (c.ρ (u * k) (f x))) = c.ρ (u * k) (c' (f.symm (f x)))
    rw [map_mul, hc.1 k hk, mul_one, ← h2 u hu, f.symm_apply_apply, f.symm_apply_apply, h1 u hu]
  have ha' : ∀ w, cv w = a • f (bcVV σ lam w) := fun w => by
    rw [← ha, ← hc']
    exact congrArg c' (f.symm_apply_apply _).symm
  refine ⟨a, fun h => h0 (LinearMap.ext fun w => by rw [ha', h, zero_smul]; rfl), fun w v => ?_⟩
  rw [ha', map_smul, LinearMap.smul_apply, hfp, smul_eq_mul, pairBK_apply, hpol]
  rfl

end Group

end GlobalTheory.TopVal.Scalar

end

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TopVal.exists_jVal_smul : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} {l : I.Laws} {Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), Formalism.L2.Forms.gramP (I.rec7 l Z) = 1 → ∀ (u : B.Word) (cv : GlobalTheory.TopVal.Val B →ₛₗ[B.embLL] (pk W).cX.W), GlobalTheory.TopVal.ValEqv W cv → cv ≠ 0 → ∀ j₀, GlobalTheory.Core.Rk.Top.IsJ u (pk W).MX j₀ → ∃ a : ℂ, a ≠ 0 ∧ GlobalTheory.TopVal.JVal W cv (a • j₀) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u cv hcv h0 j₀ hJ
  have hm := W.Q.charW.base.models
  have hr := hJ.range
  rw [GlobalTheory.Core.Rk.Top.sgT_eq_perIn_sgT I l Z u I.mu0] at hr
  have e : (fun τ => ((GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)).1 τ)⁻¹) = 1 := funext fun τ => inv_one
  obtain ⟨a, ha, h⟩ := GlobalTheory.TopVal.Scalar.exists_scalar (D := I.rec7 l Z) (M := (pk W).MX) (θ := (pk W).θ) (c := (pk W).cX)
    (pr := (pk W).prX) hm.inf (GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) _) hm.cX hm.prX
    (Formalism.L2.Forms.rankP (I.rec7 l Z)) B.wts.sgTrue B.embLL B.fields.emb
    (fun τ x => DFunLike.congr_fun (B.fields_embC τ) x) cv hcv h0 _ _ _ e j₀ hJ.inj hr hJ.eqv
  refine ⟨a, ha, fun w v => (h w v).trans ?_⟩
  unfold GlobalTheory.TopVal.pairVal
  rw [LinearMap.smul_apply]
  erw [map_smul, map_smul, LinearMap.smul_apply]
  rfl
