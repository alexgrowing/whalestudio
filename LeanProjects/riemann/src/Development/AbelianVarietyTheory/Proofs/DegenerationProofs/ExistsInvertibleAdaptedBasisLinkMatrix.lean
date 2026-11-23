import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSmulMemSpanOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.LinkMatrix

open GlobalTheory.VVRank GlobalTheory.EmbPull GlobalTheory.FieldBaseChange

theorem gs_sum' {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) {J : Type} [Fintype J]
    (a : J → Γ(Y, U)) : gs r z U (∑ i, a i) = ∑ i, gs r z U (a i) := by
  simp only [gs_eq r z U h, map_sum]

def constRing {R : Type} [CommRing R] {Z : Scheme.{0}} (π : Z ⟶ Sp R) (z : Z) : R →+* Z.presheaf.stalk z :=
  ((Z.presheaf.germ (π ⁻¹ᵁ ⊤) z trivial).hom.comp (π.app ⊤).hom).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem constVal_eq {R : Type} [CommRing R] {Z : Scheme.{0}} (π : Z ⟶ Sp R) (z : Z) (c : R) :
    constVal π z c = constRing π z c := gs_eq π z ⊤ trivial _

theorem constRing_valR {F : Type} [CommRing F] {X : Scheme.{0}} (y : Sp F ⟶ X) (V : X.Opens)
    (ht : ⊤ ≤ y ⁻¹ᵁ V) (s : Γ(X, V)) (z : Sp F) : constRing (𝟙 _) z (valR y V s) = gs y z V s := by
  rw [← constVal_eq, constVal, valR, dif_pos ht, Iso.hom_inv_id_apply]
  refine (gs_res (𝟙 _) z ht trivial _).trans ((gs_pull (𝟙 _) y z V (ht trivial) s).trans ?_)
  rw [Category.id_comp]

theorem mem_span_pullM (hS : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) (n : ℕ) (hn : 1 ≤ n)
    {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (p : T'.left) (hp : ∀ q, q = p) (h : T' ⟶ T)
    (x : SecM P.A P.L n T') : x ∈ Submodule.span Γ(T'.left, ⊤) (Set.range (pullM P.A P.L n h)) := by
  obtain ⟨V, hV, b, hb⟩ := hS S P n hn (T.hom (h.left p))
  obtain ⟨f, hf, hpf⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V) ⟨h.left p, hV⟩ trivial
  let W := T.left.basicOpen f
  let l : overRes W ⟶ overRes (T := baseOver S) V := Over.homMk
    (IsOpenImmersion.lift V.ι (W.ι ≫ T.hom) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      exact hf y.2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
  let k₀ : T'.left ⟶ W.toScheme := IsOpenImmersion.lift W.ι h.left (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      rw [hp y]
      exact hpf)
  have hk₀ : k₀ ≫ W.ι = h.left := IsOpenImmersion.lift_fac _ _ _
  let k : T' ⟶ overRes W := Over.homMk k₀ (by
    change k₀ ≫ W.ι ≫ T.hom = T'.hom
    rw [← Category.assoc, hk₀, Over.w])
  have hk : k ≫ overResι W = h := Over.OverMorphism.ext hk₀
  obtain ⟨c, hc⟩ := exists_basis P n b hb T' (k ≫ l)
  have hu : IsUnit (h.left.appTop.hom f) := by
    refine T'.left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y _ => ?_
    have : y ∈ T'.left.basicOpen (h.left.appTop.hom f) := by
      rw [← Scheme.preimage_basicOpen_top, hp y]; exact hpf
    exact (Scheme.mem_basicOpen_top _ _ _).1 this
  rw [← c.sum_repr x]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  obtain ⟨m, u, hu'⟩ := exists_pow_extend_secM P n f (pullM P.A P.L n l (SecM.ofSec P.A (b i)))
  have e₁ := congrArg (pullM P.A P.L n k) hu'
  rw [LinearMap.map_smulₛₗ, pullM_comp _ P.isLB, pullM_comp _ P.isLB, hk, ← hc] at e₁
  have e₂ : k.left.appTop.hom ((overResι W).left.appTop.hom (f ^ m)) = h.left.appTop.hom f ^ m :=
    (congrArg (fun q => q.left.appTop.hom (f ^ m)) hk).trans (map_pow h.left.appTop.hom f m)
  rw [e₂] at e₁
  obtain ⟨v, hv⟩ := (hu.pow m).exists_left_inv
  have : c i = v • pullM P.A P.L n h u := by rw [e₁, smul_smul, hv, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, rfl⟩)

theorem exists_comb (hS : SecBaseChangeAnySt) {R K : Type} [CommRing R] [Field K] (P : PolAV (Sp R)) (n : ℕ)
    (hn : 1 ≤ n) {J : Type} [Fintype J] (s : J → LB.Sec (LPow P.A P.L n (baseOver (Sp R))))
    (hs : ∀ σ : LB.Sec (LPow P.A P.L n (baseOver (Sp R))), ∃ c : J → Γ((baseOver (Sp R)).left, ⊤),
      ∀ j, σ.f j = ∑ i, liftFun P.A _ (c i) * (s i).f j)
    (y : R →+* K) {Y : Scheme.{0}} {g : Y ⟶ P.A.left} {π : Y ⟶ Sp K} (H : IsPullback g π P.A.hom (spMap y)) :
    ∃ h : Y ⟶ (baseOver (Sp R) ⊗ P.A).left, h ≫ (snd (baseOver (Sp R)) P.A).left = g ∧
      ∀ t : LB.Sec (LB.LinComb P.L (K := Fin 1) (fun _ => g) (fun _ => (n : ℤ))), ∃ b : J → K,
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : Fin 1 → P.L.ι), r z ∈ LB.wchart P.L (fun _ => g) j →
          gs r z (LB.wchart P.L (fun _ => g) j) (t.f j) = ∑ i, constVal (r ≫ π) z (b i) *
            gs (r ≫ h) z (LB.wchart P.L (fun _ => (snd (baseOver (Sp R)) P.A).left) j) ((s i).f j) := by
  let T : Over (Sp R) := Over.mk (spMap y)
  have : IsAffine T.left := inferInstanceAs (IsAffine (Sp K))
  have : IsAffine (baseOver (Sp R)).left := inferInstanceAs (IsAffine (Sp R))
  let h₀ : T ⟶ baseOver (Sp R) := Over.homMk (spMap y) (Category.comp_id _)
  let θ : Y ≅ (T ⊗ P.A).left := H.flip.isoPullback
  have θ₁ : θ.hom ≫ (fst T P.A).left = π := H.flip.isoPullback_hom_fst
  have θ₂ : θ.hom ≫ (snd T P.A).left = g := H.flip.isoPullback_hom_snd
  have θ₃ : θ.inv ≫ g = (snd T P.A).left := H.flip.isoPullback_inv_snd
  refine ⟨θ.hom ≫ (h₀ ▷ P.A).left, by rw [Category.assoc, whisker_snd_left, θ₂], fun t => ?_⟩
  let t' : LB.Sec (LPow P.A P.L n T) := pullTo t θ.inv (fun _ => θ₃)
  have m₁ := mem_span_pullM hS P n hn (T' := T) (IsLocalRing.closedPoint K)
    (fun q => Subsingleton.elim (α := PrimeSpectrum K) _ _) h₀ (SecM.ofSec P.A t')
  have m₂ : SecM.ofSec P.A t' ∈ Submodule.span Γ(T.left, ⊤)
      (Set.range fun i => pullM P.A P.L n h₀ (SecM.ofSec P.A (s i))) := by
    refine Submodule.span_le.2 ?_ m₁
    rintro _ ⟨u, rfl⟩
    obtain ⟨c, hc⟩ := hs (SecM.toSec P.A u)
    have : u = ∑ i, c i • SecM.ofSec P.A (s i) := by
      refine Subtype.ext (funext fun j => ?_)
      rw [Submodule.coe_sum, Finset.sum_apply]
      exact hc j
    rw [this, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 m₂
  have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv
  choose b hb using fun i => bij.2 (c i)
  refine ⟨b, fun Z r z j hz => ?_⟩
  have hz' : (r ≫ θ.hom) z ∈ LB.wchart P.L (fun _ : Fin 1 => (snd T P.A).left) j :=
    wchart_le_of_eq θ.hom (fun _ => θ₂) j hz
  have e₁ := gs_pullTo t θ.inv (fun _ => θ₃) (r ≫ θ.hom) z j hz'
  rw [Category.assoc, θ.hom_inv_id, Category.comp_id] at e₁
  have e₂ : t'.f j = ∑ i, liftFun P.A _ (c i) * (pullS P.A n h₀ (s i)).f j := by
    have := congrArg (fun q => q.1 j) hc
    simp only [Submodule.coe_sum] at this
    exact this.symm.trans (Finset.sum_apply _ _ _)
  refine e₁.symm.trans ((congrArg (gs (r ≫ θ.hom) z _) e₂).trans ?_)
  refine (gs_sum' _ z _ hz' _).trans (Finset.sum_congr rfl fun i _ => (gs_mul _ z _ hz' _ _).trans
    (congrArg₂ (· * ·) ?_ ?_))
  · rw [← hb, ← θ₁, ← Category.assoc]
    exact gs_const (fst T P.A).left (r ≫ θ.hom) z _ hz' (b i)
  · rw [← Category.assoc]
    exact gs_pullTo (s i) _ _ (r ≫ θ.hom) z j hz'

theorem linearIndependent_generic {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : Unif I D A G) (k : ℕ) (hk : 1 ≤ k) {J : Type} [Fintype J]
    (σ : J → IntSec U.toUnifPre k) (f : J → ∀ α, IntTerm D k α) (cls : J → D.toPre.X)
    (hE : ∀ i e, U.toUnifPre.ExpandsAt e k (σ i) (f i))
    (hF : ∀ i, ∃ s : Fam D.toPre (FractionRing R) k, FamOf D.toPre _ (f i) s)
    (hz : ∀ i i₀, cls i ≠ cls i₀ → f i (cls i₀) = 0)
    (hB : ∀ i₀, IsBasisB D.toPre (fun i : {i // cls i = cls i₀} => f i (cls i₀))) :
    LinearIndependent (FractionRing R) (fun i => genericSec U.toUnifPre k (σ i)) := by
  choose F hF using hF
  have := D.toPre.P.isAb.smooth
  have : Flat D.toPre.P.A.hom := inferInstance
  have e : (TF (R := R) (FractionRing R)).hom = jK R := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]; rfl
  have hd : IsDominant (TF (R := R) (FractionRing R)).hom := DVR.GC.isDominant_jFR (V := R) (FractionRing R)
  have h₁ : IsSchemeTheoreticallyDominant (TF (R := R) (FractionRing R)).hom := .of_isDominant _
  have h₅ : QuasiCompact (jK R) :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  have h₃ : QuasiCompact (TF (R := R) (FractionRing R)).hom := e ▸ h₅
  have h₆ : IsSchemeTheoreticallyDominant (DegPre.prB D.toPre (FractionRing R)).left :=
    .of_isPullback (IsPullback.of_hasPullback (TF (R := R) (FractionRing R)).hom D.toPre.P.A.hom)
  have h₇ : QuasiCompact (DegPre.prB D.toPre (FractionRing R)).left :=
    inferInstanceAs (QuasiCompact (pullback.snd (TF (R := R) (FractionRing R)).hom D.toPre.P.A.hom))
  have inj : ∀ α, Function.Injective (genericTerm D k α) := fun α =>
    GlobalTheory.ConstFam.pullOver_injective_of_dominant _ _ _ _
  have hF' : ∀ i α, genericTerm D k α (f i α) = famProj D.toPre _ k α (F i) := fun i α => by
    have := (secScal_iff (prB_hom D.toPre (FractionRing R))
      (famφ_prB D.toPre (FractionRing R) α) D.toPre.P.isLB (famProj D.toPre _ k α (F i)) (f i α) _
      (algebraMap R (FractionRing R)) (bf_hom D.toPre (FractionRing R)) 1).1 (by
        have e₁ : scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by unfold scal; rw [map_one, map_one]
        rw [e₁]; exact hF i α)
    rwa [map_one, one_smul] at this
  refine Fintype.linearIndependent_iff.2 fun c hc i₀ => ?_
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) c
  choose a ha using hd
  let x : IntSec U.toUnifPre k × ∀ α, IntTerm D k α := ∑ i, a i • (σ i, f i)
  have hx : x ∈ expansionPairs U.toUnifPre k :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hE i)
  have x₁ : x.1 = ∑ i, a i • σ i := Prod.fst_sum
  have x₂ : ∀ α, x.2 α = ∑ i, a i • f i α := fun α => by
    have : x.2 = ∑ i, a i • f i := Prod.snd_sum
    rw [this, Finset.sum_apply]; rfl
  have g₁ : genericSec U.toUnifPre k x.1 = 0 := by
    rw [x₁, map_sum, ← smul_zero (algebraMap R (FractionRing R) d), ← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, ha, smul_smul, Algebra.smul_def]
  have g₂ : ∀ α, genericTerm D k α (x.2 α) =
      famProj D.toPre _ k α (∑ i, algebraMap R (FractionRing R) (a i) • F i) := fun α => by
    rw [x₂, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, map_smul, hF']
  have E₁ := (expands_iff U.toUnifPre k 0 (∑ i, algebraMap R (FractionRing R) (a i) • F i)).2
    ⟨1, one_ne_zero, x, hx, by rw [g₁, smul_zero], fun α => by rw [g₂, map_one, one_smul]⟩
  have E₂ := (expands_iff U.toUnifPre k 0 0).2
    ⟨1, one_ne_zero, 0, Submodule.zero_mem _, by rw [Prod.fst_zero, map_zero, smul_zero], fun α => by
      rw [map_zero, smul_zero]; exact map_zero _⟩
  have z := ((U.expand k hk).1 _).unique E₁ E₂
  have z₂ : ∑ i : {i // cls i = cls i₀}, a i • f i (cls i₀) = 0 := by
    have := inj _ ((g₂ (cls i₀)).trans (by rw [z, map_zero]; exact (map_zero _).symm))
    rw [x₂] at this
    rw [← this, ← Finset.sum_subtype (Finset.univ.filter fun i => cls i = cls i₀) (by simp)
      (fun i => a i • f i (cls i₀)), Finset.sum_filter_of_ne]
    intro i _ h
    by_contra h'
    exact h (by rw [hz i i₀ h', smul_zero])
  have z₃ := (hB i₀ (0 : IntTerm D k (cls i₀))).unique (y₁ := fun i => a i) (y₂ := 0) (fun j => by
    have := congrArg (chartLin _ _ j) z₂
    rw [map_sum] at this
    exact this.symm) (fun j => by
    have := congrArg (chartLin _ _ j) (show ∑ i : {i // cls i = cls i₀}, (0 : R) • f i (cls i₀) = 0 by simp)
    rw [map_sum] at this
    exact this.symm)
  have z₄ : a i₀ = 0 := congrFun z₃ ⟨i₀, rfl⟩
  have := ha i₀
  rw [z₄, map_zero, Algebra.smul_def] at this
  exact (mul_eq_zero.1 this.symm).resolve_left (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2)

theorem exists_link : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (f : S.J → ∀ α, u.D.toPre.SecB S.N α), u.Basis l S.N σ cls f → ∃ b : Matrix S.J S.J (FractionRing u.V), b.det ≠ 0 ∧ u.Link σ b := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u l σ cls f ⟨_, b₂, _, b₄, b₅, b₆, b₇⟩
  have hN : 1 ≤ S.N := by
    rw [ρ.N_eq]
    exact Nat.one_le_pow _ _ (pow_pos ρ.n_prime.pos _)
  have li := linearIndependent_generic u.U S.N hN σ f cls b₄ b₅ (fun i i₀ h => SecOver.ext _ _ fun j =>
    b₆ i (cls i₀) (fun m hm => h (b₂ i₀ i ⟨m, hm⟩).symm) j) b₇
  have e₁ : u.U.gen.inv.left ≫ u.U.gen.hom.left = 𝟙 _ := congrArg (fun q => q.left) u.U.gen.inv_hom_id
  have e₂ : u.U.gen.hom.left ≫ u.U.gen.inv.left = 𝟙 _ := congrArg (fun q => q.left) u.U.gen.hom_inv_id
  let gn : pullback u.G.hom (jK u.V) ⟶ u.A.A.left := u.U.gen.hom.left
  let π : pullback u.G.hom (jK u.V) ⟶ Sp (FractionRing u.V) := pullback.snd u.G.hom (jK u.V)
  let q : pullback u.G.hom (jK u.V) ⟶ u.G.left := pullback.fst u.G.hom (jK u.V)
  have : IsIso gn := ⟨⟨u.U.gen.inv.left, e₂, e₁⟩⟩
  have H₀ : IsPullback gn π u.A.A.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨(Over.w u.U.gen.hom).trans (Category.comp_id _).symm⟩
  have H : IsPullback (gn ≫ u.φ) π ρ.P.A.hom (spMap u.yK) := by
    have := H₀.paste_horiz u.cart.1
    rwa [Category.id_comp] at this
  obtain ⟨h, hh, hc⟩ := exists_comb hL.2.1.secBaseChangeAny ρ.P S.N hN ρ.s (fun t => (ρ.s_basis t).exists) u.yK H
  let M₁ := LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => q) (fun _ => (S.N : ℤ))
  let M₂ := LB.LinComb ρ.P.L (K := Fin 1) (fun _ => gn ≫ u.φ) (fun _ => (S.N : ℤ))
  have l₁ : M₁.IsLB := DVR.linComb_isLB _ u.U.LG.isLB _ _
  have l₂ : M₂.IsLB := DVR.linComb_isLB _ ρ.P.isLB _ _
  obtain ⟨w, hw⟩ : LBIso M₁ M₂ := by
    obtain ⟨w₀, hw₀⟩ := u.lb
    exact LBIso.trans l₁ (DVR.linComb_isLB _ u.A.isLB _ _) l₂
      (GlobalTheory.GenericSectionBasis.iso_pow gn u.U.gen.inv.left e₁ e₂ q u.U.ext S.N)
      (iso_linComb ((isGen_iff w₀).1 hw₀) (fun _ : Fin 1 => gn) (fun _ => (S.N : ℤ)))
  obtain ⟨w', hw', hww⟩ := GlobalTheory.GenericSectionBasis.exists_inv_iso w hw
  let σK : S.J → SecOver π M₁ := fun i => genericSec u.U.toUnifPre S.N (σ i)
  choose b hb using fun i => hc (DVR.secOfIso (σK i) hw' l₂ l₁)
  have key : ∀ (i) (Z : Scheme.{0}) (r : Z ⟶ pullback u.G.hom (jK u.V)) (z : Z) (a₁ : M₁.ι) (a₂ : M₂.ι),
      r z ∈ M₁.U a₁ → r z ∈ M₂.U a₂ →
      (gm r z ((LB.div M₂ M₁).U (a₂, a₁)) (w.s (a₂, a₁))).val * gs r z (M₁.U a₁) ((σK i).f a₁) =
        ∑ j, constRing (r ≫ π) z (b i j) *
          gs (r ≫ h) z (LB.wchart ρ.P.L (fun _ => (snd (baseOver (Sp S.R)) ρ.P.A).left) a₂) ((ρ.s j).f a₂) := by
    intro i Z r z a₁ a₂ m₁ m₂
    have t₁ := GlobalTheory.GenericGenerated.gs_secOfIso w' (σK i) hw' l₂ l₁ a₂ a₁ r z ⟨m₂, m₁⟩
    rw [hww Z r z a₁ a₂ ⟨m₁, m₂⟩, inv_inv] at t₁
    simp only [← constVal_eq]
    exact t₁.symm.trans (hb i Z r z a₂ m₂)
  refine ⟨Matrix.of b, fun hdet => ?_, fun a v ⟨a', ha', l', c, hl', hv⟩ => ?_⟩
  · obtain ⟨c, hc₀, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    refine hc₀ (funext (Fintype.linearIndependent_iff.1 li c (SecOver.ext _ _ fun a₁ => fn_ext fun y hy => ?_)))
    obtain ⟨a₂, m₂⟩ := exists_chart l₂ y
    have t₁ : chartFun π M₁ a₁ (∑ i, c i • σK i) = ∑ i, c i • chartFun π M₁ a₁ (σK i) :=
      map_sum (chartLin π M₁ a₁) _ _
    refine (congrArg (gs (𝟙 _) y (M₁.U a₁)) t₁).trans ((gs_sum' _ y _ hy _).trans
      (Eq.trans ?_ (gs_zero' _ y _ hy).symm))
    refine (Finset.sum_congr rfl fun i _ => gs_smul π (𝟙 _) y (M₁.U a₁) hy (c i) _).trans ?_
    refine (Units.mul_right_eq_zero (gm (𝟙 _) y ((LB.div M₂ M₁).U (a₂, a₁)) (w.s (a₂, a₁)))).1 ?_
    rw [Finset.mul_sum]
    refine (Finset.sum_congr rfl fun i _ => (mul_left_comm _ _ _).trans
      (congrArg₂ (· * ·) (constVal_eq _ _ _) (key i _ (𝟙 _) y a₁ a₂ hy m₂))).trans ?_
    simp only [Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : ∑ i, c i * b i j = 0 := congrFun hc j
    rw [← Finset.sum_mul, ← map_sum, this, map_zero, zero_mul]
  · let r : Sp (PadicAlgCl p) ⟶ pullback u.G.hom (jK u.V) := a.left
    let z : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
    have s₁ : a' ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = (r ≫ h) ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left := by
      rw [Category.assoc, hh]; exact ha'
    obtain rfl : a' = r ≫ h :=
      (cancel_mono (pullback.snd (𝟙 (Sp S.R)) ρ.P.A.hom)).1 s₁
    obtain ⟨a₁, m₁⟩ := exists_chart l₁ (r z)
    have m₂ : r z ∈ M₂.U l' := mem_wchart_of_eq h (fun _ => hh) (r z) l' (hl' trivial)
    have m₃ : (r ≫ q) z ∈ (u.H S.N).U a₁ := (wchart_eq (fun _ => (Category.comp_id q).symm) a₁).le m₁
    have n₃ : ⊤ ≤ (r ≫ q) ⁻¹ᵁ (u.H S.N).U a₁ := (CrdCalc.top_le_iff _ _).2 m₃
    have m₄ : r z ∈ (LB.div M₂ M₁).U (l', a₁) := ⟨m₂, m₁⟩
    have n₄ : ⊤ ≤ r ⁻¹ᵁ (LB.div M₂ M₁).U (l', a₁) := (CrdCalc.top_le_iff _ _).2 m₄
    refine ⟨a₁, c * Units.map (CrdCalc.valHom r _ n₄).toMonoidHom (w.s (l', a₁)), n₃, fun i => ?_⟩
    apply (constRing (𝟙 (Sp (PadicAlgCl p))) z).injective
    have t₁ : constRing (𝟙 _) z (CrdCalc.valHom r _ n₄ (w.s (l', a₁)).val) =
        (gm r z ((LB.div M₂ M₁).U (l', a₁)) (w.s (l', a₁))).val := by
      rw [← CrdCalc.valR_eq, constRing_valR r _ n₄, gs_unit r z _ m₄]
    have t₂ : constRing (𝟙 _) z (valR (u.toG a) ((u.H S.N).U a₁) ((σ i).f a₁)) =
        gs r z (M₁.U a₁) ((σK i).f a₁) :=
      (constRing_valR (r ≫ q) _ n₃ _ z).trans (gs_pullFn (π := u.G.hom) (π' := π) pullback.condition
        (wchart_eq (fun _ => (Category.comp_id q).symm) a₁).le _ r z m₁).symm
    have t₃ : ∀ x, constRing (r ≫ π) z x = constRing (𝟙 _) z (algebraMap _ (PadicAlgCl p) x) := fun x => by
      have : r ≫ π = 𝟙 _ ≫ spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) :=
        (Over.w a).trans (Category.id_comp _).symm
      rw [this, ← constVal_eq, ← constVal_eq, constVal_specMap]
    rw [Units.val_mul, _root_.mul_assoc, map_mul, map_mul, t₂]
    refine Eq.trans ?_ (congrArg _ ((congrArg (· * _) t₁).trans (key i _ r z a₁ l' m₁ m₂))).symm
    rw [Finset.mul_sum, Matrix.mulVec, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hv j, map_mul, map_mul, t₃, mul_left_comm]
    exact congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) rfl (constRing_valR (r ≫ h) _ hl' _ z))

end GlobalTheory.ZH.LinkMatrix
end
