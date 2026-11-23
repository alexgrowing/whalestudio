import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutsSecOfIsLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UltrametricCoefficientBound
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.LineNorm (IsTanBasis)
open GlobalTheory.Twist (resM resM_resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
open GlobalTheory.OmegaHT
open GlobalTheory.VB (IsFrame)

namespace GlobalTheory.OmegaHT.Bundle

open GlobalTheory.ChainPts.FrameNorm (valHom valF_eq_valHom valHom_resG norm_valF_le_one norm_le_one_iff)

theorem linearIndependent_of_smul_mem {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] {r : ℕ}
    (b : Module.Basis (Fin r) R M) (η : Fin r → M) {c : R} (hc : c ≠ 0)
    (h : ∀ i, c • b i ∈ Submodule.span R (Set.range η)) : LinearIndependent R η := by
  rw [linearIndependent_iff_card_le_finrank_span]
  haveI : Module.Finite R (Submodule.span R (Set.range η)) := Module.Finite.span_of_finite R (Set.finite_range η)
  have li : LinearIndependent R fun i => (⟨c • b i, h i⟩ : Submodule.span R (Set.range η)) := by
    refine LinearIndependent.of_comp (Submodule.span R (Set.range η)).subtype ?_
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    have := Fintype.linearIndependent_iff.1 b.linearIndependent (fun i => g i * c)
      (by simp only [mul_smul]; exact hg) i
    exact (mul_eq_zero.1 this).resolve_right hc
  exact li.fintype_card_le_finrank

theorem resM_mem_span {X : Scheme.{0}} {F : X.Modules} {r : ℕ} {V U : X.Opens} (h : U ≤ V) (η : Fin r → Γ(F, V))
    {σ : Γ(F, V)} (hσ : σ ∈ Submodule.span Γ(X, V) (Set.range η)) :
    resM F h σ ∈ Submodule.span Γ(X, U) (Set.range fun l => resM F h (η l)) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hσ
  rw [map_sum]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [GlobalTheory.Twist.resM_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

theorem linearIndependent_of_holdsP {X : Scheme.{0}} [AlgebraicGeometry.IsIntegral X] {p : ℕ}
    (hp : ∀ U : X.Opens, (U : Set X).Nonempty → (p : Γ(X, U)) ≠ 0) {F : X.Modules} {r : ℕ} {V : X.Opens}
    {η : Fin r → Γ(F, V)} (hη : SectionsSatisfyAtPrime p η) (U : X.Opens) (h : U ≤ V) :
    LinearIndependent Γ(X, U) fun l => resM F h (η l) := by
  rcases (U : Set X).eq_empty_or_nonempty with hU | hU
  · obtain rfl : U = ⊥ := TopologicalSpace.Opens.ext hU
    exact linearIndependent_of_subsingleton
  · haveI : Nonempty U := hU.to_subtype
    obtain ⟨f, hf, hfp⟩ := hη
    refine linearIndependent_of_smul_mem (hf.basis h) _ (hp U hU) fun i => ?_
    have := resM_mem_span h η (hfp i)
    rwa [GlobalTheory.Twist.resM_smul, map_natCast, ← hf.basis_apply h] at this

theorem natCast_ne_zero_of_flat {O : Type} [CommRing O] [IsDomain O] [CharZero O] {X : Scheme.{0}} (s : X ⟶ Sp O)
    [Flat s] {p : ℕ} (hp : p ≠ 0) (U : X.Opens) (hU : (U : Set X).Nonempty) : (p : Γ(X, U)) ≠ 0 := by
  obtain ⟨z, hz⟩ := hU
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hz U.2
  haveI : Nonempty V := ⟨⟨z, hzV⟩⟩
  intro h0
  have h1 : (p : Γ(X, V)) = 0 := by
    rw [← map_natCast (resG X (show V ≤ U from hVU)), h0, map_zero]
  have hfl : (s.appLE ⊤ V le_top).hom.Flat :=
    HasRingHomProperty.appLE @Flat s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  let e := (Scheme.ΓSpecIso (CommRingCat.of O)).commRingCatIsoToRingEquiv
  have hfl' : ((s.appLE ⊤ V le_top).hom.comp e.symm.toRingHom).Flat :=
    RingHom.Flat.comp (RingHom.Flat.of_bijective e.symm.bijective) hfl
  letI := ((s.appLE ⊤ V le_top).hom.comp e.symm.toRingHom).toAlgebra
  haveI : Module.Flat O Γ(X, V) := hfl'
  have hp' : (p : O) ∈ nonZeroDivisors O := mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hp)
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(X, V)) hp'
  have : (1 : Γ(X, V)) = 0 := hreg (by
    change (p : O) • (1 : Γ(X, V)) = (p : O) • (0 : Γ(X, V))
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, nsmul_one, h1, nsmul_zero])
  exact one_ne_zero this

theorem size_eq {X : Scheme.{0}} {F : X.Modules} {g r : ℕ} {V U : X.Opens} {f : Fin g → Γ(F, V)} {s : Fin r → Γ(F, U)}
    (hf : IsFrame f) (hs : IsFrame s) {z : X} (hV : z ∈ V) (hU : z ∈ U) : g = r := by
  haveI : Nonempty (V ⊓ U : X.Opens) := ⟨⟨z, hV, hU⟩⟩
  have h1 := Module.finrank_eq_card_basis (hf.basis (inf_le_left : V ⊓ U ≤ V))
  have h2 := Module.finrank_eq_card_basis (hs.basis (inf_le_right : V ⊓ U ≤ U))
  simpa using h1.symm.trans h2

theorem crd_sum {X : Scheme.{0}} {F : X.Modules} {g r : ℕ} {V V' : X.Opens} {s : Fin r → Γ(F, V')} (hs : IsFrame s)
    (c : Fin g → Γ(X, V)) (f : Fin g → Γ(F, V)) (i : Fin r) :
    crd hs (∑ l, c l • f l) i = ∑ l, resG X inf_le_left (c l) * crd hs (f l) i := by
  simp only [crd, map_sum, GlobalTheory.Twist.resM_smul, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

theorem crd_app {X : Scheme.{0}} {F G : X.Modules} (ι : G ⟶ F) {r : ℕ} {V V' : X.Opens} {e : Fin r → Γ(G, V')}
    {s : Fin r → Γ(F, V')} (he : IsFrame e) (hs : IsFrame s) (hι : ∀ l, ι.app _ (e l) = s l) (σ : Γ(G, V)) (i : Fin r) :
    crd he σ i = crd hs (ι.app _ σ) i := by
  have nat : ∀ {U U' : X.Opens} (h : U' ≤ U) (τ : Γ(G, U)), resM F h (ι.app _ τ) = ι.app _ (resM G h τ) :=
    fun h τ => (ConcreteCategory.congr_hom (ι.mapPresheaf.naturality (homOfLE h).op) τ).symm
  have key : resM F (inf_le_left : V ⊓ V' ≤ V) (ι.app _ σ) = ∑ l, crd he σ l • hs.basis inf_le_right l := by
    rw [nat]
    conv_lhs => rw [← (he.basis (inf_le_right : V ⊓ V' ≤ V')).sum_repr (resM G inf_le_left σ)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Scheme.Modules.Hom.app_smul, he.basis_apply, hs.basis_apply, ← nat, hι]
    rfl
  conv_rhs => rw [crd, key]
  rw [Module.Basis.repr_sum_self]

theorem exists_ringHom {X : Scheme.{0}} {R k : Type} [CommRing R] [Field k] (σ : R →+* k) (w : Sp R ⟶ X)
    (V : X.affineOpens) (hw : ⊤ ≤ w ⁻¹ᵁ V.1) :
    ∃ κ : Γ(X, V.1) →+* R, spMap κ ≫ V.2.fromSpec = w ∧ ∀ c, valF (spMap σ ≫ w) V.1 c = σ (κ c) := by
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (w.appLE V.1 ⊤ hw).hom, ?_, fun a => ?_⟩
  · have h := IsAffineOpen.SpecMap_appLE_fromSpec w V.2 (isAffineOpen_top _) hw
    rw [IsAffineOpen.fromSpec_top] at h
    rw [spMap_comp, Category.assoc]
    change Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ Spec.map (w.appLE V.1 ⊤ hw) ≫ V.2.fromSpec = w
    rw [h, ← Scheme.isoSpec_Spec_hom, Iso.hom_inv_id_assoc]
  · have h' : ⊤ ≤ (spMap σ ≫ w) ⁻¹ᵁ V.1 := fun q _ => hw (Set.mem_univ (spMap σ q))
    rw [valF, dif_pos h']
    have e : (spMap σ ≫ w).appLE V.1 ⊤ h' = w.appLE V.1 ⊤ hw ≫ (spMap σ).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE (spMap σ) w V.1 ⊤ ⊤ hw le_rfl).symm
    have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ)
    have n' := congrArg (fun q => q.hom ((w.appLE V.1 ⊤ hw).hom a)) n
    rw [e]
    exact n'

theorem exists_center {X : Scheme.{0}} (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    (w : Sp ↥(intO C) ⟶ X) : ∃ z : X, ∀ V : X.Opens, z ∈ V → ⊤ ≤ w ⁻¹ᵁ V := by
  haveI : IsLocalRing ↥(intO C) := by
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
    have unit : ∀ b : ↥(intO C), ‖(b : C)‖ = 1 → IsUnit b := fun b hb => by
      have hb0 : (b : C) ≠ 0 := fun h => by simp [h] at hb
      refine IsUnit.of_mul_eq_one (⟨(b : C)⁻¹, ?_⟩ : ↥(intO C)) (Subtype.ext (mul_inv_cancel₀ hb0))
      change ‖(b : C)⁻¹‖ ≤ 1
      rw [norm_inv, hb, inv_one]
    have ha : ‖(a : C)‖ ≤ 1 := a.2
    rcases ha.eq_or_lt with h | h
    · exact Or.inl (unit a h)
    · refine Or.inr (unit _ ?_)
      change ‖(1 : C) - a‖ = 1
      rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simpa using h.ne'), norm_one, norm_neg,
        max_eq_left h.le]
  exact ⟨w (closedPoint ↥(intO C)), fun V hV => (Scheme.preimage_eq_top_of_closedPoint_mem w hV).ge⟩

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem not_le_chart (Z : LocM.Mdl Y i₀) (hp : p.Prime) (y : Z.Pt) (a : Fin Z.m) : ¬ ⊤ ≤ y.z ⁻¹ᵁ (Z.U a).1 := by
  intro hz
  have h1 := norm_valF_le_one (↥y.C.S) y.z (Z.U a).1 hz (Z.alg a (p : ↥Z.i.c.F)⁻¹)
  have h' : ⊤ ≤ (spMap (intO ↥y.C.S).subtype ≫ y.z) ⁻¹ᵁ (Z.U a).1 :=
    fun q _ => hz (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))
  rw [valF_eq_valHom _ _ h'] at h1
  have e : valHom _ _ h' (Z.alg a (p : ↥Z.i.c.F)⁻¹) = (p : ↥y.C.S)⁻¹ := by
    have := map_inv₀ ((valHom _ _ h').comp (Z.alg a)) (p : ↥Z.i.c.F)
    rwa [map_natCast] at this
  rw [e, norm_inv, y.C.norm_p, inv_inv] at h1
  exact absurd (by exact_mod_cast h1 : p ≤ 1) hp.one_lt.not_ge

theorem exists_sections (Z : LocM.Mdl Y i₀) {X : Scheme.{0}} (h : X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw)
    {F : X.Modules} {s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)} (hs : ∀ a, IsFrame (s a)) (hF : GlobalTheory.VB.IsVB F r)
    (hd : HasDualFrames Z h x hs) (hb : LocBasis (Y Z.i).t p (h ≫ Z.π)) (z : X) :
    ∃ (V : X.Opens) (η : Fin r → Γ(F, V)), z ∈ V ∧ SectionsSatisfyAtPrime p η ∧ CutsSec Z h x true hs η := by
  obtain ⟨V, g, e, η, hz, he, ⟨M, hM⟩, hc⟩ := hb z
  obtain ⟨f, hf, hfd⟩ := hd V g e he
  obtain ⟨U, f', hzU, hf'⟩ := hF z
  obtain rfl : g = r := size_eq hf hf' hz hzU
  refine ⟨V.1, fun j => ∑ l, η j l • f l, hz, ⟨f, hf, fun i => ?_⟩, ?_⟩
  · refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨M i, ?_⟩
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hM, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · intro y w hw a φ hφ hV cf v hv
    obtain ⟨κ, hκ, hval⟩ := exists_ringHom (intO ↥y.C.S).subtype w V hV
    have e1 : spMap ((intO ↥y.C.S).subtype.comp κ) ≫ V.2.fromSpec = spMap (intO ↥y.C.S).subtype ≫ w := by
      rw [spMap_comp, Category.assoc, hκ]
    have e2 : spMap ((intO ↥y.C.S).subtype.comp κ) ≫ V.2.fromSpec ≫ h = y.gen := by
      rw [← Category.assoc, e1, Category.assoc, hw]; rfl
    have e3 : spMap ((intO ↥y.C.S).subtype.comp κ) ≫ V.2.fromSpec ≫ h ≫ Z.π = y.gen ≫ Z.π := by
      rw [← e2, Category.assoc, Category.assoc]
    have hv' := hfd (↥y.C.S) ((intO ↥y.C.S).subtype.comp κ) a φ (hφ.trans e2.symm) cf v (by rw [e3]; exact hv)
    have hc' := hc y.C κ _ v hv'
    rw [e3, e1] at hc'
    refine hc'.trans (forall_congr' fun j => ?_)
    have hU : ⊤ ≤ (spMap (intO ↥y.C.S).subtype ≫ w) ⁻¹ᵁ (V.1 ⊓ h ⁻¹ᵁ (Z.U a).1) := fun q _ => by
      refine ⟨hV (Set.mem_univ (spMap (intO ↥y.C.S).subtype q)), ?_⟩
      have : ((spMap (intO ↥y.C.S).subtype ≫ w) ≫ h) q ∈ (Z.U a).1 := by
        rw [← e1, Category.assoc, e2, ← hφ]
        have hr : Set.range (Z.chart a) = (Z.U a).1 := (Z.U a).2.range_fromSpec
        exact hr.le ⟨spMap φ q, rfl⟩
      exact this
    have key : ∀ i, valF (spMap (intO ↥y.C.S).subtype ≫ w) _ (crd (hs a) (∑ l, η j l • f l) i) =
        ∑ l, (κ (η j l) : ↥y.C.S) * valF (spMap (intO ↥y.C.S).subtype ≫ w) _ (crd (hs a) (f l) i) := fun i => by
      rw [crd_sum, valF_eq_valHom _ _ hU, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, valHom_resG, hval, valF_eq_valHom _ _ hU]
      rfl
    have eq : ∑ i, cf i * valF (spMap (intO ↥y.C.S).subtype ≫ w) _ (crd (hs a) (∑ l, η j l • f l) i) =
        ∑ l, (κ (η j l) : ↥y.C.S) * ∑ i, cf i * valF (spMap (intO ↥y.C.S).subtype ≫ w) _ (crd (hs a) (f l) i) := by
      simp only [key, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [eq]

end Model

theorem bundle_of_locBasis : GlobalTheory.OmegaHT.LinkSt → GlobalTheory.OmegaHT.SpanSt → GlobalTheory.OmegaHT.GlueSt → GlobalTheory.OmegaHT.BundleSt := by
  intro hL hS hG E _ _ _ H Dw Xo p W Y i₀ Z hp hW _ B hB h ho r x hx hb
  obtain ⟨F, s, k, hF, hd⟩ := hL E H Dw Xo p W Y i₀ Z B.X h r x hx
  choose V η hz hP hC using exists_sections Z h x k.frame hF hd hb
  haveI := B.isIntegral
  haveI := B.flat
  have hp0 := natCast_ne_zero_of_flat B.str hp.ne_zero
  let V' : B.X ⊕ Fin Z.m → B.X.Opens := fun α => Sum.rec V (fun a => h ⁻¹ᵁ (Z.U a).1) α
  let η' : ∀ α, Fin r → Γ(F, V' α) := fun α => Sum.rec (motive := fun α => Fin r → Γ(F, V' α)) η s α
  have hP' : ∀ α, SectionsSatisfyAtPrime p (η' α) := by
    rintro (z | a)
    · exact hP z
    · exact ⟨s a, k.frame a, fun i => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)⟩
  have hC' : ∀ α, CutsSec Z h x true k.frame (η' α) := by
    rintro (z | a)
    · exact hC z
    · intro y w hw _ _ _ hV
      refine absurd ?_ (not_le_chart Z hp y a)
      rw [← hw]
      exact hV
  obtain ⟨G, ι, hGr, he⟩ := hG B.X F r (B.X ⊕ Fin Z.m) V' η' (fun z => ⟨Sum.inl z, hz z⟩)
    (fun α U hU => linearIndependent_of_holdsP hp0 (hP' α) U hU)
    (fun α β => hS E H Dw Xo p W Y i₀ Z hp hW B hB h ho r x true F s k.frame _ _ _ _ (hP' α) (hP' β) (hC' α) (hC' β))
  choose e hef heι using he
  have hs' : ∀ a : Fin Z.m, IsFrame (F := G) (U := h ⁻¹ᵁ (Z.U a).1) (e (Sum.inr a)) := fun a => hef (Sum.inr a)
  have tr : ∀ (a : Fin Z.m) (α) (l i : Fin r),
      GlobalTheory.ChainPts.coef true (hef α) (hs' a) l i = crd (k.frame a) (η' α l) i := fun a α l i => by
    rw [coef_true, crd_app ι (hs' a) (k.frame a) (heι (Sum.inr a)), heι]
  refine ⟨G, fun a => e (Sum.inr a), hGr, hs', ?_, ?_⟩
  · intro K _ w a a' φ φ' hφ hφ' j
    exact Eq.mpr (congrArg (fun c => IsCombAtG (Y Z.i).t _ _ c _)
      (funext fun i => congrArg (valF w _) (tr a' (Sum.inr a) i j))) (k.glue K w a a' φ φ' hφ hφ' j)
  · intro y w hw a φ hφ U f hf hU cf v hv
    obtain ⟨z, hc⟩ := exists_center (↥y.C.S) w
    have hV := hc _ (hz z)
    refine (hC z y w hw a φ hφ hV cf v hv).trans ?_
    refine Iff.trans ?_ (norm_le_one_iff true (hef (Sum.inl z)) hf (hs' a) (↥y.C.S) w hV hU cf)
    refine forall_congr' fun l => Iff.of_eq (congrArg (fun c => ‖c‖ ≤ 1) (Finset.sum_congr rfl fun i _ => ?_))
    exact congrArg (fun c => cf i * valF _ _ c) (tr a (Sum.inl z) l i).symm

end GlobalTheory.OmegaHT.Bundle

end
