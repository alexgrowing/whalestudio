import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulAntiOfUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexFormsFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesComplexForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.Columns.CoefColLemmas

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix
open Formalism.L2.Theta Formalism.MainNotions.StandardLattice GlobalTheory.Mem.Th Filter Topology
open Formalism.IndefR.Lev (finE swapAE EAf)
open scoped TensorProduct

namespace GlobalTheory.Mem.ColAd

section Tr

variable {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ)

def frL (u : ι → GL (Fin n) ℂ) (y : Frames G) : Frames G :=
  ⟨fun τ => (u τ : Matrix (Fin n) (Fin n) ℂ) * y.1 τ, fun τ => by
    rw [det_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (u τ).isUnit).mul (y.2 τ)⟩

def lT (u : ι → GL (Fin n) ℂ) : (Frames G → ℂ) →ₗ[ℂ] (Frames G → ℂ) := LinearMap.funLeft ℂ ℂ (frL G u)

omit [Fintype ι] in

theorem lT_apply (u : ι → GL (Fin n) ℂ) (F : Frames G → ℂ) (y : Frames G) : lT G u F y = F (frL G u y) := rfl

omit [Fintype ι] in

theorem lT_mul (u v : ι → GL (Fin n) ℂ) (F : Frames G → ℂ) : lT G (u * v) F = lT G v (lT G u F) :=
  funext fun y => congrArg F (Subtype.ext (funext fun τ => Matrix.mul_assoc _ _ _))

omit [Fintype ι] in

theorem lT_one (F : Frames G → ℂ) : lT G 1 F = F :=
  funext fun y => congrArg F (Subtype.ext (funext fun τ => Matrix.one_mul _))

theorem lT_mem (lam : ι → DomWeight n) (u : ι → GL (Fin n) ℂ) {F : Frames G → ℂ} (hF : F ∈ ValC G lam) :
    lT G u F ∈ ValC G lam := by
  obtain ⟨P, hP, rfl⟩ := hF
  have h1 : CSpan lam ≤ VV ℂ lam := by
    refine (CSpan_le_span (RingHom.id ℂ) lam).trans ?_
    rw [Submodule.span_le]
    rintro _ ⟨F', hF', rfl⟩
    simpa [MvPolynomial.map_id] using hF'
  have h2 : Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (u τ : Matrix (Fin n) (Fin n) ℂ)) P ∈ VV ℂ lam :=
    (Formalism.GradedWeylDivisibility.blockActTensor ℂ ℂ ι n n _).2 (fun τ => nablaSq ℂ n (lam τ)) (fun τ => nablaSq ℂ n (lam τ))
      (fun τ f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ _ f hf) P (h1 hP)
  have h3 : Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (u τ : Matrix (Fin n) (Fin n) ℂ)) P ∈ CSpan lam := by
    simpa [MvPolynomial.map_id] using map_mem_CSpan (RingHom.id ℂ) lam _ h2
  refine ⟨(∏ τ, (u τ : Matrix (Fin n) (Fin n) ℂ).det ^ shiftOf lam τ) • _, Submodule.smul_mem _ _ h3, ?_⟩
  funext y
  rw [map_smul, Pi.smul_apply, smul_eq_mul, lT_apply]
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul, frL, det_mul, mul_zpow, Finset.prod_mul_distrib,
    mul_assoc, Formalism.GradedWeylDivisibility.blockAct, eval_aeval_poly]
  congr 3
  simp [Matrix.mul_apply]

theorem continuous_lT (lam : ι → DomWeight n) [FiniteDimensional ℂ (ValC G lam)] (l : (Frames G → ℂ) →ₗ[ℂ] ℂ) {F : Frames G → ℂ}
    (hF : F ∈ ValC G lam) {X : Type} [TopologicalSpace X] {u : X → ι → GL (Fin n) ℂ}
    (hu : ∀ τ, Continuous fun x => (u x τ : Matrix (Fin n) (Fin n) ℂ)) : Continuous fun x => l (lT G (u x) F) := by
  have h1 : Continuous fun x => (⟨lT G (u x) F, lT_mem G lam _ hF⟩ : ValC G lam) := by
    refine Continuous.subtype_mk (continuous_pi fun y => ?_) _
    obtain ⟨P, -, rfl⟩ := hF
    simp only [lT_apply, fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul]
    refine (continuous_finsetProd _ fun τ _ => ?_).mul ((MvPolynomial.continuous_eval P).comp (continuous_pi fun v => ?_))
    · exact (((hu τ).matrix_mul continuous_const).matrix_det).zpow₀ _ fun x => Or.inl ((frL G (u x) y).2 τ).ne_zero
    · exact ((hu v.1).matrix_mul continuous_const).matrix_elem _ _
  exact (l ∘ₗ (ValC G lam).subtype).continuous_of_finiteDimensional.comp h1

end Tr

section Val

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ)

def valL (b : S.β) (d : S.D b) : (S.Cl → Fr emb σ n → ℂ) →ₗ[ℂ] (Fr emb σ n → ℂ) :=
  (S.trTo emb σ b d).toLinearMap ∘ₗ LinearMap.proj (S.cl b d)

omit [StarRing E] [NumberField K] [StarRing K] in

theorem tr_mul (b : S.β) (g h : S.G b) (F : Fr emb σ n → ℂ) :
    S.tr emb σ b (g * h) F = S.tr emb σ b g (S.tr emb σ b h F) := by
  funext y
  simp only [GStep.tr, trFr_apply, map_mul, Units.val_mul, _root_.mul_inv_rev, frMul_mul, mul_assoc]

variable {S emb σ} {lam : ι → DomWeight n} {φ : S.Cl → Fr emb σ n → ℂ}

theorem valL_eq (hφ : φ ∈ S.Fi emb σ lam) (c : S.Cl) (g : S.G c.1) :
    valL S emb σ c.1 (g • S.rep c) φ = S.tr emb σ c.1 g (φ c) := by
  obtain ⟨b, q⟩ := c
  have hq : (Quotient.mk _ (g • S.rp b q) : MulAction.orbitRel.Quotient (S.G b) (S.D b)) = q :=
    (Quotient.sound (show (MulAction.orbitRel (S.G b) (S.D b)).r (g • S.rp b q) (S.rp b q) from ⟨g, rfl⟩)).trans (S.rp_spec b q)
  have h1 : S.mv b (g • S.rp b q) • S.rp b (Quotient.mk _ (g • S.rp b q)) = g • S.rp b q := S.mv_smul b _
  rw [hq] at h1
  have h2 := (hφ ⟨b, q⟩).2 ⟨g⁻¹ * S.mv b (g • S.rp b q), by
    show (g⁻¹ * S.mv b (g • S.rp b q)) • S.rp b q = S.rp b q
    rw [mul_smul, h1, inv_smul_smul]⟩
  show S.tr emb σ b (S.mv b (g • S.rp b q)) (φ ⟨b, Quotient.mk _ (g • S.rp b q)⟩) = S.tr emb σ b g (φ ⟨b, q⟩)
  rw [hq, ← h2]
  refine Eq.trans ?_ (tr_mul S emb σ b g _ _)
  rw [mul_inv_cancel_left]
  exact congrArg _ h2

theorem valL_smul (hφ : φ ∈ S.Fi emb σ lam) (b : S.β) (g : S.G b) (d : S.D b) :
    valL S emb σ b (g • d) φ = S.tr emb σ b g (valL S emb σ b d φ) := by
  have h := valL_eq hφ (S.cl b d) (g * S.mv b d)
  rw [mul_smul, S.mv_smul, tr_mul] at h
  exact h

theorem valL_rep (hφ : φ ∈ S.Fi emb σ lam) (c : S.Cl) : valL S emb σ c.1 (S.rep c) φ = φ c := by
  have := valL_eq hφ c 1
  rwa [one_smul, DiaStab.tr_one] at this

theorem valL_mem (hφ : φ ∈ S.Fi emb σ lam) (b : S.β) (d : S.D b) : valL S emb σ b d φ ∈ ValC (Gr emb σ n) lam :=
  DiaStab.tr_mem S emb σ lam b _ (hφ _).1

variable (S emb σ lam) in

def prFi : (S.Cl → Fr emb σ n → ℂ) →ₗ[ℂ] S.Fi emb σ lam :=
  (LinearMap.exists_leftInverse_of_injective (S.Fi emb σ lam).subtype (Submodule.ker_subtype _)).choose

omit [StarRing E] [NumberField K] [StarRing K] in

theorem prFi_of_mem (hφ : φ ∈ S.Fi emb σ lam) : prFi S emb σ lam φ = ⟨φ, hφ⟩ :=
  LinearMap.congr_fun (LinearMap.exists_leftInverse_of_injective (S.Fi emb σ lam).subtype (Submodule.ker_subtype _)).choose_spec
    ⟨φ, hφ⟩

end Val

section Comp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : InfF D) (V : HSp D) {n : ℕ} (hn : V.rank = n) {ι : Type} (t : ι ≃ D.what₂.Tau)

def finN : GA D V →* GL (Fin n) (AfE D.host.F D.host.E) := by
  subst hn
  exact finE V

def infN : GA D V →* (ι → GL (Fin n) ℂ) := by
  subst hn
  exact MonoidHom.pi fun τ => (Formalism.UG.bc (θ (t τ))).comp (infHom V)

theorem finN_apply (g : GA D V) (i j : Fin n) : (finN V hn g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)) i j =
    (finE V g).1 (Fin.cast hn.symm i) (Fin.cast hn.symm j) := by
  subst hn
  rfl

theorem infN_apply (g : GA D V) (τ : ι) (i j : Fin n) : (infN θ V hn t g τ : Matrix (Fin n) (Fin n) ℂ) i j =
    infMat D.sp.cm.sig V.gram (θ (t τ)) g (Fin.cast hn.symm i) (Fin.cast hn.symm j) := by
  subst hn
  rfl

variable {V}

theorem finN_of_inf {k : GA D V} (hk : k ∈ GinfC V) : finN V hn k = 1 := by
  subst hn
  show Formalism.UG.bc (swapAE D) (finHom V k) = 1
  rw [show finHom V k = 1 from hk, map_one]

theorem infN_of_fin {k : GA D V} (hk : k ∈ GfC V) : infN θ V hn t k = 1 := by
  subst hn
  funext τ
  show Formalism.UG.bc (θ (t τ)) (infHom V k) = 1
  rw [show infHom V k = 1 from hk, map_one]

theorem swapAE_sig (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    swapAE D (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig z) = Formalism.UG.sigR D.sp.cm.sig _ (swapAE D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb, RingHom.map_add, RingHom.map_add]

theorem JR_one (hG : V.gram = 1) (A : Type) [CommRing A] [Algebra D.host.F A] : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (F := D.host.F) A V.gram = 1 := by
  rw [hG, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_one _ (map_zero _) (map_one _)]

theorem finN_mem (hG : V.gram = 1) (g : GA D V) : finN V hn g ∈ UAd D.sp.cm n := by
  subst hn
  have h : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig) (finHom V g).1 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR _ V.gram * (finHom V g).1 =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR _ V.gram := GlobalTheory.UnitarySplit.finHom_mem V g
  rw [JR_one hG, mul_one] at h
  have h2 := congrArg (fun M => Matrix.map M (swapAE D)) h
  simp only [Matrix.map_mul] at h2
  rw [PtExist.mem_uad_iff, ← Matrix.map_one (swapAE D) (map_zero _) (map_one _), ← h2]
  congr 1
  exact Matrix.ext fun i j => (swapAE_sig _).symm

theorem exists_point (hθ : IsInfFam θ) (hG : V.gram = 1) {x : GL (Fin n) (AfE D.host.F D.host.E)} (hx : x ∈ UAd D.sp.cm n)
    (u : ι → Matrix (Fin n) (Fin n) ℂ) (hu : ∀ τ, (u τ)ᴴ * u τ = 1) :
    ∃ g : GA D V, finN V hn g = x ∧ ∀ τ, (infN θ V hn t g τ : Matrix (Fin n) (Fin n) ℂ) = u τ := by
  subst hn
  have R := GlobalTheory.SmoothForms.RealPts.realPoints D |>.2 θ hθ V
  obtain ⟨a, a1, a2⟩ := R.2.1 (fun τ => u (t.symm τ)) fun τ => by
    show (u (t.symm τ))ᴴ * gramAt D V τ * u (t.symm τ) = gramAt D V τ
    rw [gramAt, hG, Matrix.map_one _ (map_zero _) (map_one _), mul_one, hu]
  let s := (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).toRingEquiv
  have hs : ∀ z, swapAE D (s.symm z) = z := s.apply_symm_apply
  let x' := Formalism.UG.bc s.symm.toRingHom x
  have hx' : x' ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram := by
    show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig) x'.1 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR _ V.gram * x'.1 = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR _ V.gram
    rw [JR_one hG, mul_one]
    apply Matrix.map_injective (f := swapAE D) s.injective
    simp only [Matrix.map_mul]
    rw [Matrix.map_one _ (map_zero _) (map_one _), ← (PtExist.mem_uad_iff x).1 hx]
    congr 1
    · exact Matrix.ext fun i j => (swapAE_sig _).trans (congrArg _ (hs _))
    · exact Matrix.ext fun i j => hs _
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 x' (one_mem _) hx'
  refine ⟨a * k, ?_, fun τ => ?_⟩
  · rw [map_mul, finN_of_inf rfl a1, one_mul]
    show Formalism.UG.bc (swapAE D) (finHom V k) = x
    rw [k2]
    exact Units.ext (Matrix.ext fun i j => hs _)
  · rw [map_mul, infN_of_fin θ rfl t k1, mul_one]
    exact (a2 (t τ)).trans (by rw [t.symm_apply_apply])

theorem exists_rat (hθ : IsInfFam θ) (hG : V.gram = 1) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ δ : URat D.sp.cm n, finN V hn γ = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ.1 ∧
      ∀ τ, (infN θ V hn t γ τ : Matrix (Fin n) (Fin n) ℂ) = (δ.1 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D (t τ)) := by
  subst hn
  obtain ⟨δ, hδ, e⟩ := hγ
  rw [hG] at hδ
  refine ⟨⟨δ, hδ⟩, ?_, fun τ => ?_⟩
  · show Formalism.UG.bc _ (Formalism.UG.bc _ (matHom V γ)) = _
    rw [show matHom V γ = _ from e.symm]
    rfl
  · show (Formalism.UG.bc _ (Formalism.UG.bc _ (matHom V γ))).1 = _
    rw [show matHom V γ = _ from e.symm]
    exact Matrix.ext fun i j => (hθ (t τ)).1 _

theorem continuous_infN (hθ : IsInfFam θ) (τ : ι) : Continuous fun g => (infN θ V hn t g τ : Matrix (Fin n) (Fin n) ℂ) := by
  subst hn
  exact GlobalTheory.Mem.VolExists.continuous_infMat V.gram (hθ (t τ))

open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem eventually_congOne (x₀ : GL (Fin n) (AfE D.host.F D.host.E)) (a : 𝓞 D.host.E) :
    ∀ᶠ κ in 𝓝 (1 : GA D V), CongOne a (x₀⁻¹ * finN V hn κ * x₀) := by
  subst hn
  letI := rlt_top D.host.F D.host.E
  haveI := rlt_isModTop D.host.F D.host.E
  haveI := rlt_topRing (F := D.host.F) (E := D.host.E)
  haveI : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    ⟨rfl⟩
  have hs : Continuous (swapAE D) := by
    haveI := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (EAf D)
    refine (IsModuleTopology.continuous_of_linearMap
      (LinearEquiv.ofBijective (rlt_comm (F := D.host.F) (E := D.host.E)) (TensorProduct.comm _ _ _).bijective).symm.toLinearMap).congr
      fun z => ?_
    refine (LinearEquiv.symm_apply_eq _).2 ?_
    exact ((Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm_apply_apply z).symm
  have hf : Continuous fun κ : GA D V => (finN V rfl κ).1 :=
    (GlobalTheory.Mem.VolExists.continuous_finMat (σ := D.sp.cm.sig) V.gram).matrix_map hs
  simp only [CongOne, Filter.eventually_all]
  intro i j
  have hc : Continuous fun κ : GA D V => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ * ((x₀⁻¹ * finN V rfl κ * x₀).1 i j - (1 : Matrix _ _ (AfE D.host.F D.host.E)) i j) :=
    continuous_const.mul ((((continuous_const.matrix_mul hf).matrix_mul continuous_const).matrix_elem i j).sub continuous_const)
  refine (rlt_isOpen_intAf.preimage hc).mem_nhds ?_
  simp

theorem isAutFunDef_of [Fintype ι] (hθ : IsInfFam θ) (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n)
    [FiniteDimensional ℂ (ValC G lam)] (Φ : GA D V → Frames G → ℂ) (h1 : ∀ g, Φ g ∈ ValC G lam)
    (h2 : ∀ γ ∈ GQ V, ∀ g, lT G (infN θ V hn t γ) (Φ (γ * g)) = Φ g) (h3 : ∀ᶠ κ in 𝓝 (1 : GA D V), ∀ g, Φ (g * κ) = Φ g)
    (h4 : ∀ k ∈ GinfC V, ∀ g, Φ (g * k) = Φ g) (l : (Frames G → ℂ) →ₗ[ℂ] ℂ) :
    IsAutFunDef V fun g => l (lT G (infN θ V hn t g) (Φ g)) := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  refine ⟨⟨fun γ hγ g => by rw [map_mul, lT_mul, h2 γ hγ], ?_, continuous_iff_continuousAt.2 fun g₀ => ?_⟩, ?_⟩
  · let U : Subgroup (GA D V) :=
      { carrier := {κ | ∀ g, Φ (g * κ) = Φ g}
        one_mem' := fun g => by rw [mul_one]
        mul_mem' := fun {a b} ha hb g => by rw [← mul_assoc, hb, ha]
        inv_mem' := fun {a} ha g => by rw [← ha, inv_mul_cancel_right] }
    exact ⟨U, Subgroup.isOpen_of_mem_nhds U (g := 1) h3, fun k hk hk' g => by
      rw [map_mul, infN_of_fin θ hn t hk', mul_one, hk g]⟩
  · refine (continuous_lT G lam l (h1 g₀) (continuous_infN θ hn t hθ)).continuousAt.congr ?_
    have ht : Tendsto (fun g : GA D V => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
      have := (continuous_const_mul g₀⁻¹).tendsto g₀
      rwa [inv_mul_cancel] at this
    filter_upwards [ht.eventually h3] with g hg
    rw [← hg g₀, mul_inv_cancel_left]
  · let Ψ : Module.Dual ℂ (ValC G lam) →ₗ[ℂ] (GA D V → ℂ) :=
      LinearMap.pi fun g => Module.Dual.eval ℂ _ ⟨_, lT_mem G lam (infN θ V hn t g) (h1 g)⟩
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range Ψ) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨l ∘ₗ lT G (infN θ V hn t k) ∘ₗ (ValC G lam).subtype, funext fun g => ?_⟩
    show l (lT G (infN θ V hn t k) (lT G (infN θ V hn t g) (Φ g))) = l (lT G (infN θ V hn t (g * k)) (Φ (g * k)))
    rw [map_mul, lT_mul, h4 k hk]

theorem isAniso_of_gram (hG : V.gram = 1) : IsAniso V := by
  rintro r C ⟨hr, hC, h0⟩
  have h1 := congrFun (congrFun h0 ⟨0, hr⟩) ⟨0, hr⟩
  rw [hG, Matrix.mul_one, Matrix.mul_apply] at h1
  have h2 := congrArg D.host.φ₀ h1
  have h3 : ∀ a : D.host.E, D.host.φ₀ (star a) = starRingEnd ℂ (D.host.φ₀ a) := D.sp.cm.cmUnram.2.1 _
  have h4 : ∑ i, Complex.normSq (D.host.φ₀ (C i ⟨0, hr⟩)) = 0 := by
    apply Complex.ofReal_injective
    rw [map_sum] at h2
    rw [Complex.ofReal_sum, Complex.ofReal_zero, ← map_zero D.host.φ₀]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h2
    rw [map_mul, Complex.normSq_eq_conj_mul_self, ← h3]
    rfl
  refine hC.ne_zero ⟨0, hr⟩ (funext fun i => ?_)
  have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _).1 h4 i (Finset.mem_univ i)
  simpa using this

theorem mem_cuspS (hθ : IsInfFam θ) (hG : V.gram = 1) (hs : V.SigOK) (hd : V.IsDefinite) {φ : GA D V → ℂ} (h : IsAutFunDef V φ) :
    φ ∈ CuspS θ V := by
  rw [CuspS_eq_of_aniso θ (isAniso_of_gram hG)]
  exact Submodule.subset_span ((GlobalTheory.DefiniteForms.autFunDefIffSm D θ hθ V hs hd φ).1 h)

end Comp

end GlobalTheory.Mem.ColAd

end
