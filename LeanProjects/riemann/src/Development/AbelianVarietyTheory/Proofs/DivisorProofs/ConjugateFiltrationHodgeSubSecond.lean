import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham GlobalTheory.DeRhamSheaf TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConjSeq.RankConj

open GlobalTheory.Published.AbelianDeRham (bcMor)

section Algebra

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {M M' : Type*} [AddCommGroup M]
  [Module R M] [AddCommGroup M'] [Module R' M'] (f : M →ₛₗ[algebraMap R R'] M') (P : Submodule R M)

def bcSub : R' ⊗[R] P →ₗ[R'] M' := liftSemi (f.comp P.subtype)

theorem bcSub_tmul (x : R') (y : P) : bcSub f P (x ⊗ₜ y) = x • f y := rfl

theorem bcSub_eq : bcSub f P = liftSemi f ∘ₗ P.subtype.baseChange R' := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rw [LinearMap.comp_apply, LinearMap.baseChange_tmul, bcSub_tmul, liftSemi_tmul]; rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb]

variable {f P}

theorem bcSub_injective (hf : Function.Bijective (liftSemi f)) {N : Submodule R M} (h : IsCompl P N) :
    Function.Injective (bcSub f P) := by
  rw [bcSub_eq]
  refine hf.1.comp fun a b hab => ?_
  have hid : Submodule.linearProjOfIsCompl P N h ∘ₗ P.subtype = LinearMap.id :=
    LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left h x
  have := congrArg ((Submodule.linearProjOfIsCompl P N h).baseChange R') hab
  rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
    hid, LinearMap.baseChange_id, LinearMap.id_apply, LinearMap.id_apply] at this

variable (f P)

theorem range_bcSub : LinearMap.range (bcSub f P) = Submodule.span R' (f '' P) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [bcSub_tmul]
      exact (Submodule.span R' _).smul_mem x (Submodule.subset_span ⟨y, y.2, rfl⟩)
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨1 ⊗ₜ ⟨y, hy⟩, by rw [bcSub_tmul, one_smul]⟩

variable {f P}

def bcSubEquiv (hf : Function.Bijective (liftSemi f)) {N : Submodule R M} (h : IsCompl P N) :
    R' ⊗[R] P ≃ₗ[R'] Submodule.span R' (f '' P) :=
  (LinearEquiv.ofInjective _ (bcSub_injective hf h)).trans (LinearEquiv.ofEq _ _ (range_bcSub f P))

theorem bcSubEquiv_apply (hf : Function.Bijective (liftSemi f)) {N : Submodule R M} (h : IsCompl P N)
    (z : R' ⊗[R] P) : (bcSubEquiv hf h z : M') = bcSub f P z := rfl

end Algebra

variable (p : ℕ) [Fact p.Prime]

theorem pull_frobDR {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (hR : (p : R) = 0)
    (hR' : (p : R') = 0) {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A']
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ) (x : primDR A) :
    (bcMor h).pull (frobDR p R hR A x) = frobDR p R' hR' A' ((bcMor h).pull x) := by
  have m'' := (frobMor p R hR A (cast_left p R hR A)).comp (bcMor h)
  have e : ∀ r, frobR p R' hR' (algebraMap R R' r) = ((algebraMap R R').comp (frobR p R hR)) r :=
    fun r => by rw [RingHom.comp_apply, frobR_apply, frobR_apply, map_pow]
  have e' : GlobalTheory.VB.frob A'.left p (cast_left p R' hR' A') ≫ φ = φ ≫ GlobalTheory.VB.frob A.left p (cast_left p R hR A) :=
    GlobalTheory.VB.frob_naturality p (cast_left p R hR A) φ (cast_left p R' hR' A')
  exact (GrpMor.pull_pull _ _ m'' (fun _ => rfl) rfl x).trans
    (GrpMor.pull_pull (bcMor h) (frobMor p R' hR' A' (cast_left p R' hR' A')) m'' e e' x).symm

theorem conjDR_bc {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (hR : (p : R) = 0)
    (hR' : (p : R') = 0) {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A']
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ)
    (hbc : (bcMor h).IsBC) :
    conjDR p R' hR' A' = Submodule.span R' ((bcMor h).pull '' conjDR p R hR A) := by
  apply le_antisymm
  · rw [conjDR, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    obtain ⟨t, rfl⟩ := hbc.2 z
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | tmul x y =>
      rw [liftSemi_tmul, LinearMap.map_smulₛₗ, ← pull_frobDR p hR hR' h]
      exact (Submodule.span R' _).smul_mem _ (Submodule.subset_span ⟨_, Submodule.subset_span ⟨y, rfl⟩, rfl⟩)
    | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb
  · rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      rw [pull_frobDR p hR hR' h]
      exact Submodule.subset_span ⟨_, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

theorem conjDR_summand (hCF : GlobalTheory.Published.ConjugateFiltration) {R : Type} [CommRing R]
    (hR : (p : R) = 0) (A : Over (Sp R)) [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) :
    (∃ N, IsCompl (conjDR p R hR A) N) ∧
      ∀ P : PrimeSpectrum R, Module.rankAtStalk (conjDR p R hR A) P = g :=
  have h := hCF p R hR A g hA hg (cast_left p R hR A) (frobMor p R hR A (cast_left p R hR A))
  ⟨h.2.1, h.2.2.1⟩

section Sheaf

variable {p} {T : Scheme.{0}} (hT : (p : Γ(T, ⊤)) = 0) (A : Over T) [GrpObj A] {H : T.Modules}
  (E : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV))
  (C : GlobalTheory.VB.Sub H)
  (hC : ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      s ∈ C.sec V ↔ E V hV s ∈ conjDR p Γ(T, V) (GlobalTheory.SS.FrobField.cast_zero hT V) (onAff A hV))

def secEquiv (W : T.Opens) (hW : IsAffineOpen W) :
    Γ(C.toMod, W) ≃ₗ[Γ(T, W)] conjDR p Γ(T, W) (GlobalTheory.SS.FrobField.cast_zero hT W) (onAff A hW) :=
  LinearEquiv.ofBijective
    (((E W hW).toLinearMap ∘ₗ GlobalTheory.QCoh.appLinear C.incl W).codRestrict _
      fun s => (hC W hW _).1 (C.incl_app_mem s))
    ⟨fun s t hst => C.incl_app_injective W ((E W hW).injective (congrArg Subtype.val hst)),
     fun y =>
      have hy : (E W hW).symm y ∈ C.sec W :=
        (hC W hW _).2 (by rw [LinearEquiv.apply_symm_apply]; exact y.2)
      ⟨C.mkSec _ hy, Subtype.ext ((congrArg (E W hW) (C.incl_app_mkSec _ hy)).trans
        ((E W hW).apply_symm_apply _))⟩⟩

theorem secEquiv_apply (W : T.Opens) (hW : IsAffineOpen W) (s : Γ(C.toMod, W)) :
    (secEquiv hT A E C hC W hW s : primDR (onAff A hW)) = E W hW (C.incl.app W s) := rfl

include hC in

theorem isFrame (hCF : GlobalTheory.Published.ConjugateFiltration) (hBC : GlobalTheory.Published.AbelianDeRham.BaseChange)
    {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (hE : IsDRIso A H E)
    {D : T.Opens} (hD : IsAffineOpen D)
    (c : Module.Basis (Fin g) Γ(T, D) (conjDR p Γ(T, D) (GlobalTheory.SS.FrobField.cast_zero hT D) (onAff A hD)))
    (σ : Fin g → Γ(C.toMod, D)) (hσ : ∀ i, C.incl.app D (σ i) = (E D hD).symm (c i)) :
    GlobalTheory.VB.IsFrame σ := by
  refine GlobalTheory.VB.isFrame_of_forall_exists fun V h y hy => ?_
  obtain ⟨W, hW, hyW, hle⟩ := GlobalTheory.QCoh.exists_affine_mem_le y hy
  refine ⟨W, hle, hyW, ?_⟩
  letI := resAlg (hle.trans h)
  obtain ⟨φ, hφ, hφ'⟩ := GlobalTheory.DeRhamSheaf.VB.exists_transition A hD hW (hle.trans h)
  have hbc : (bcMor hφ).IsBC :=
    (hBC _ (onAff A hD) g (GlobalTheory.DeRhamSheaf.VB.isAbelianScheme_onAff A hA hD)
      (GlobalTheory.DeRhamSheaf.VB.smooth_onAff A hg hD) _ (onAff A hW) φ hφ).1
  obtain ⟨N, hN⟩ := (conjDR_summand p hCF (GlobalTheory.SS.FrobField.cast_zero hT D) (onAff A hD)
    (GlobalTheory.DeRhamSheaf.VB.isAbelianScheme_onAff A hA hD) (GlobalTheory.DeRhamSheaf.VB.smooth_onAff A hg hD)).1
  have hspan := conjDR_bc p (GlobalTheory.SS.FrobField.cast_zero hT D) (GlobalTheory.SS.FrobField.cast_zero hT W) hφ hbc
  let b0 := (Algebra.TensorProduct.basis Γ(T, W) c).map (bcSubEquiv hbc hN)
  let d := (b0.map (LinearEquiv.ofEq _ _ hspan.symm)).map (secEquiv hT A E C hC W hW).symm
  have hd (i : Fin g) : d i = GlobalTheory.Twist.resM C.toMod (hle.trans h) (σ i) := by
    apply (secEquiv hT A E C hC W hW).injective
    apply Subtype.ext
    simp only [d, Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
    have e1 : C.incl.app W (GlobalTheory.Twist.resM C.toMod (hle.trans h) (σ i)) =
        GlobalTheory.Twist.resM H (hle.trans h) ((E D hD).symm (c i)) :=
      (GlobalTheory.Twist.app_resM C.incl (hle.trans h) (σ i)).trans (congrArg _ (hσ i))
    have e2 : E W hW (GlobalTheory.Twist.resM H (hle.trans h) ((E D hD).symm (c i))) = (bcMor hφ).pull (c i) :=
      (hE D W hD hW (hle.trans h) φ hφ hφ' _).trans (congrArg _ (LinearEquiv.apply_symm_apply _ _))
    have e3 : ((b0 i : Submodule.span Γ(T, W) ((bcMor hφ).pull '' (conjDR p Γ(T, D)
        (GlobalTheory.SS.FrobField.cast_zero hT D) (onAff A hD)))) : primDR (onAff A hW)) = (bcMor hφ).pull (c i) := by
      simp only [b0, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
      refine (bcSubEquiv_apply hbc hN _).trans ?_
      exact (bcSub_tmul _ _ 1 (c i)).trans (one_smul _ _)
    exact (LinearEquiv.coe_ofEq_apply hspan.symm (b0 i)).trans (e3.trans (e2.symm.trans
      ((congrArg (E W hW) e1.symm).trans (secEquiv_apply hT A E C hC W hW _).symm)))
  have hl : Fintype.linearCombination Γ(T, W)
      (fun i => GlobalTheory.Twist.resM C.toMod (hle.trans h) (σ i)) = d.equivFun.symm.toLinearMap := by
    refine LinearMap.ext fun a => ?_
    rw [Fintype.linearCombination_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply]
    simp only [hd]
  rw [hl]
  exact d.equivFun.symm.bijective

end Sheaf

end GlobalTheory.ConjSeq.RankConj

namespace GlobalTheory.ConjSeq

open GlobalTheory.Published.AbelianDeRham (bcMor)
open GlobalTheory.DeRhamSheaf.VB (exists_transition isAbelianScheme_onAff smooth_onAff)
open RankConj

theorem isVB_conj : GlobalTheory.Published.ConjugateFiltration → GlobalTheory.CovTop.Hypotheses2 → ∀ (p : ℕ) [Fact p.Prime]
    {T : Scheme.{0}} [Algebra (ZMod p) Γ(T, ⊤)] (A : Over T) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)),
    IsDRIso A H e →
    ∀ C : GlobalTheory.VB.Sub H, (∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      s ∈ C.sec V ↔ e V hV s ∈ GlobalTheory.ConjSeq.conjDR p Γ(T, V)
        (GlobalTheory.SS.FrobField.cast_zero (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) V) (onAff A hV)) →
    GlobalTheory.VB.IsVB C.toMod g := by
  intro hCF hP2 p _ T _ A _ g hA hg H E hE C hC x
  have hT : (p : Γ(T, ⊤)) = 0 := GlobalTheory.VB.natCast_eq_zero T p (ZMod p)
  have hBC := hP2.p5.2.2.1
  obtain ⟨V, hV, hxV, -⟩ := GlobalTheory.QCoh.exists_affine_mem_le (U := ⊤) x trivial
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim hP2.p5.1
    (isAbelianScheme_onAff A hA hV) (smooth_onAff A hg hV)
  obtain ⟨⟨N, hN⟩, hrk⟩ := conjDR_summand p hCF (GlobalTheory.SS.FrobField.cast_zero hT V) (onAff A hV)
    (isAbelianScheme_onAff A hA hV) (smooth_onAff A hg hV)
  set P := conjDR p Γ(T, V) (GlobalTheory.SS.FrobField.cast_zero hT V) (onAff A hV) with hPdef
  haveI : Module.Finite Γ(T, V) P :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl P N hN)
      fun y => ⟨y, Submodule.linearProjOfIsCompl_apply_left hN y⟩
  haveI : Module.Projective Γ(T, V) P :=
    Module.Projective.of_split P.subtype (Submodule.linearProjOfIsCompl P N hN)
      (LinearMap.ext fun y => Submodule.linearProjOfIsCompl_apply_left hN y)
  haveI : Module.FinitePresentation Γ(T, V) P := Module.finitePresentation_of_projective _ _
  obtain ⟨y, rfl⟩ : ∃ y : V, y.1 = x := ⟨⟨x, hxV⟩, rfl⟩
  set q := hV.primeIdealOf y
  haveI : Module.Free (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl P) :=
    Module.mem_freeLocus.1 (by rw [Module.freeLocus_eq_univ]; trivial)
  have hr : Module.finrank (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl P) = g := hrk q
  obtain ⟨r, hr', b', -⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    q.asIdeal.primeCompl (LocalizedModule.mkLinearMap q.asIdeal.primeCompl P)
    (Localization.AtPrime q.asIdeal) (Module.finBasisOfFinrankEq _ _ hr)
  have hD := hV.basicOpen r
  letI := resAlg (T.basicOpen_le r)
  obtain ⟨φ, hφ, -⟩ := exists_transition A hV hD (T.basicOpen_le r)
  have hbc : (bcMor hφ).IsBC :=
    (hBC _ (onAff A hV) g (isAbelianScheme_onAff A hA hV) (smooth_onAff A hg hV) _
      (onAff A hD) φ hφ).1
  haveI := hV.isLocalization_basicOpen r
  haveI : IsLocalizedModule (Submonoid.powers r)
      (TensorProduct.mk Γ(T, V) Γ(T, T.basicOpen r) P 1) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers r) Γ(T, T.basicOpen r) _).2
      (TensorProduct.isBaseChange _ _ _)
  obtain ⟨c0⟩ := GlobalTheory.VB.nonempty_basis_of_localizedModule Γ(T, T.basicOpen r) (.powers r)
    (TensorProduct.mk Γ(T, V) Γ(T, T.basicOpen r) P 1) b'
  have hspan := conjDR_bc p (GlobalTheory.SS.FrobField.cast_zero hT V)
    (GlobalTheory.SS.FrobField.cast_zero hT (T.basicOpen r)) hφ hbc
  let c := (c0.map (bcSubEquiv hbc hN)).map (LinearEquiv.ofEq _ _ hspan.symm)
  let σ : Fin g → Γ(C.toMod, T.basicOpen r) := fun i => (secEquiv hT A E C hC _ hD).symm (c i)
  refine ⟨T.basicOpen r, σ, (GlobalTheory.QCoh.mem_primeCompl_primeIdealOf_iff hV y r).1 hr',
    isFrame hT A E C hC hCF hBC hA hg hE hD c σ fun i => ?_⟩
  apply (E _ hD).injective
  rw [LinearEquiv.apply_symm_apply, ← secEquiv_apply hT A E C hC, LinearEquiv.apply_symm_apply]

end GlobalTheory.ConjSeq
