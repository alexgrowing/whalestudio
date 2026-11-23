import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByOfSpans
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByWeightZeroStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFactorClosedImmersionDensePointsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.TestMap

theorem exists_pt {L : Type} [Field L] [IsAlgClosed L] {X T : Scheme.{0}} (f : X ⟶ T) [LocallyOfFiniteType f]
    (s : Sp L ⟶ T) {Z : Set X} (hZ : IsLocallyClosed Z) {x : X} (hx : x ∈ Z) (hs : f x ∈ Set.range s) :
    ∃ a : Sp L ⟶ X, a ≫ f = s ∧ ∀ w, a w ∈ Z := by
  have : JacobsonSpace (pullback f s : Scheme.{0}) := LocallyOfFiniteType.jacobsonSpace (pullback.snd f s)
  have h1 : x ∈ Set.range (pullback.fst f s) := by
    rw [Scheme.Pullback.range_fst]; exact hs
  obtain ⟨x', rfl⟩ := h1
  obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints (Z := (pullback.fst f s) ⁻¹' Z) ⟨x', hx⟩
    (hZ.preimage (pullback.fst f s).continuous)
  replace hc : IsClosed {c} := hc
  refine ⟨pointOfClosedPoint (pullback.snd f s) c hc ≫ pullback.fst f s, ?_, fun w => ?_⟩
  · rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  · rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
    exact hcW

theorem dense_pts {L : Type} [Field L] [IsAlgClosed L] {X T : Scheme.{0}} (f : X ⟶ T) [Smooth f]
    (s : Sp L ⟶ T) (hs : DenseRange s) : Dense (⋃ a : {a : Sp L ⟶ X // a ≫ f = s}, Set.range a.1) := by
  rw [dense_iff_inter_open]
  intro U hU hne
  have ho : IsOpenMap f := f.isOpenMap
  obtain ⟨_, ⟨x, hx, rfl⟩, hr⟩ := hs.inter_open_nonempty _ (ho U hU) (hne.image _)
  obtain ⟨a, ha, hU'⟩ := exists_pt f s hU.isLocallyClosed hx hr
  exact ⟨a (IsLocalRing.closedPoint L), hU' _, Set.mem_iUnion.2 ⟨⟨a, ha⟩, _, rfl⟩⟩

theorem ext_of_pts {L : Type} [Field L] {X Y T : Scheme.{0}} [IsReduced X] (i : Y ⟶ T) [IsSeparated i]
    {f g : X ⟶ Y} (h : f ≫ i = g ≫ i) {A : Type} (a : A → (Sp L ⟶ X)) (hd : Dense (⋃ k, Set.range (a k)))
    (H : ∀ k, a k ≫ f = a k ≫ g) : f = g := by
  have : IsDominant (Sigma.desc a) := ⟨hd.mono (Set.iUnion_subset fun k => by
    rintro _ ⟨w, rfl⟩
    exact ⟨Sigma.ι (fun _ : A => Sp L) k w, by rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]⟩)⟩
  refine ext_of_isDominant_of_isSeparated i h (Sigma.desc a) (Sigma.hom_ext _ _ fun k => ?_)
  rw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc, H]

noncomputable def comb {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {H : LB X} {J : Type} [Fintype J]
    (s : J → H.Sec) (a : J → k) : H.Sec where
  f l := ∑ j, constFn p (H.U l) (a j) * (s j).f l
  compat l l' := by
    have e : ∀ (U V : X.Opens) (h : V ≤ U) (c : k),
        (X.presheaf.map (homOfLE h).op).hom (constFn p U c) = constFn p V c := fun U V h c =>
      congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))
        (Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)
    simp only [map_sum, map_mul, e, Finset.mul_sum, (s _).compat l l']
    exact Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _

theorem crd_comb {k R : Type} [CommRing k] [CommRing R] {X : Scheme.{0}} {p : X ⟶ Sp k} {H : LB X}
    {J : Type} [Fintype J] {s : J → H.Sec} (m : Matrix J J k)
    {x : Sp R ⟶ X} {ψ : k →+* R} (hx : x ≫ p = spMap ψ) {v : J → R} (hv : Crd H s x v) :
    Crd H (fun i => comb p s (m i)) x ((m.map ψ).mulVec v) := by
  obtain ⟨l, c, hl, hv⟩ := hv
  refine ⟨l, c, hl, fun i => ?_⟩
  change ∑ j, ψ (m i j) * v j = c * valR x _ (∑ j, constFn p (H.U l) (m i j) * (s j).f l)
  rw [CrdCalc.valR_eq x _ hl, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq,
    GlobalTheory.Points.valR_constFn_of_over p ψ x hx _ hl, hv, mul_left_comm]

theorem ne_zero_iff {K : Type} [Field K] {X : Scheme.{0}} {H : LB X} {J : Type} {s : J → H.Sec}
    {x : Sp K ⟶ X} {v : J → K} (hv : Crd H s x v) :
    v ≠ 0 ↔ x (IsLocalRing.closedPoint K) ∈ ⨆ j, nonzeroLocus (s j) := by
  rw [TopologicalSpace.Opens.mem_iSup, Function.ne_iff]
  refine exists_congr fun j => ?_
  rw [← CrdCalc.top_le_iff, ← CrdCalc.crd_isUnit_iff j hv, isUnit_iff_ne_zero]
  rfl

theorem exists_mul_of_span_eq {O K J : Type} [CommRing O] [Field K] [Algebra O K] [Fintype J] [DecidableEq J]
    {B b : Matrix J J K} (h : Submodule.span O (Set.range B) ≤ Submodule.span O (Set.range b)) :
    ∃ m : Matrix J J O, B = m.map (algebraMap O K) * b := by
  have : ∀ i, ∃ c : J → O, ∑ j, c j • b j = B i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun O).1 (h (Submodule.subset_span ⟨i, rfl⟩))
  choose m hm using this
  refine ⟨Matrix.of m, ?_⟩
  ext i k
  rw [← hm i]
  simp [Matrix.mul_apply, Finset.sum_apply, Algebra.smul_def]

theorem mem_iSup_comb {k L : Type} [CommRing k] [Field L] [IsAlgClosed L] {X : Scheme.{0}} {p : X ⟶ Sp k}
    [LocallyOfFiniteType p] {H : LB X} {J : Type} [Fintype J] {s : J → H.Sec} {m : Matrix J J k}
    (hm : IsUnit m.det) (ψ : k →+* L) (h : ∀ a : Sp L ⟶ X, a ≫ p = spMap ψ → ∃ w, w ≠ 0 ∧ Crd H s a w)
    {x : X} (hx : p x ∈ Set.range (spMap ψ)) : x ∈ ⨆ i, nonzeroLocus (comb p s (m i)) := by
  by_contra hn
  obtain ⟨a, ha, hZ⟩ := exists_pt p (spMap ψ)
    (⨆ i, nonzeroLocus (comb p s (m i)) : X.Opens).isOpen.isClosed_compl.isLocallyClosed hn hx
  obtain ⟨w, hw, hc⟩ := h a ha
  refine hZ _ ((ne_zero_iff (crd_comb m ha hc)).1 fun h0 => hw ?_)
  have hd : (m.map ψ).det ≠ 0 := by
    have := (hm.map ψ).ne_zero
    rwa [RingHom.map_det] at this
  exact Matrix.eq_zero_of_mulVec_eq_zero hd h0

theorem denseRange_spMap {k L : Type} [CommRing k] [CommRing L] {ψ : k →+* L} (h : Function.Injective ψ) :
    DenseRange (spMap ψ) :=
  (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical ψ).2
    (((RingHom.injective_iff_ker_eq_bot ψ).1 h).le.trans bot_le)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}

section Test
variable {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem gPt_j : gPt p ≫ spMap u.j = jFK (R := u.V) (PadicAlgCl p) ≫ jK u.V := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem coe_j (a : u.V) :
    (u.j a : PadicAlgCl p) = algebraMap (FractionRing u.V) _ (algebraMap u.V (FractionRing u.V) a) := rfl

theorem exists_of_eq_coe {x : FractionRing u.V} {c : OO p} (h : algebraMap _ (PadicAlgCl p) x = c) :
    ∃ a : u.V, algebraMap _ _ a = x :=
  (u.norm_le x).1 (h ▸ (mem_OO_iff _).1 c.2)

theorem isLocalHom_j : IsLocalHom u.j := ⟨fun a ha => by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have h1 : algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) a) * b = 1 :=
    congrArg Subtype.val hb
  have h0 : algebraMap u.V (FractionRing u.V) a ≠ 0 := fun h => by simp [h] at h1
  obtain ⟨c, hc⟩ := exists_of_eq_coe u (x := (algebraMap u.V (FractionRing u.V) a)⁻¹) (c := b)
    (by rw [map_inv₀]; exact (eq_inv_of_mul_eq_one_right h1).symm)
  refine IsUnit.of_mul_eq_one c (IsFractionRing.injective u.V (FractionRing u.V) ?_)
  rw [map_mul, hc, map_one, mul_inv_cancel₀ h0]⟩

theorem injective_j : Function.Injective ((OO p).subtype.comp u.j) :=
  (algebraMap (FractionRing u.V) (PadicAlgCl p)).injective.comp (IsFractionRing.injective u.V (FractionRing u.V))

theorem exists_matrix {J : Type} [Fintype J] [DecidableEq J] {B b : Matrix J J (FractionRing u.V)} (hB : B.det ≠ 0)
    (h : Submodule.span (OO p) (Set.range (B.map (algebraMap _ (PadicAlgCl p)))) =
      Submodule.span (OO p) (Set.range (b.map (algebraMap _ (PadicAlgCl p))))) :
    b.det ≠ 0 ∧ ∃ m : Matrix J J u.V, IsUnit m.det ∧ B.map (algebraMap _ (PadicAlgCl p)) =
      (m.map fun a => (u.j a : PadicAlgCl p)) * b.map (algebraMap _ (PadicAlgCl p)) := by
  obtain ⟨m₁, h₁⟩ := exists_mul_of_span_eq h.le
  obtain ⟨m₂, h₂⟩ := exists_mul_of_span_eq h.ge
  set e := algebraMap (FractionRing u.V) (PadicAlgCl p)
  have hd : ∀ A : Matrix J J (FractionRing u.V), (A.map e).det = e A.det := fun A => (e.map_det A).symm
  have hd' : ∀ A : Matrix J J (OO p), (A.map (algebraMap _ (PadicAlgCl p))).det = (A.det : OO p) :=
    fun A => ((algebraMap (OO p) (PadicAlgCl p)).map_det A).symm
  have hB' : e B.det ≠ 0 := (map_ne_zero e).2 hB
  have e₁ := congrArg Matrix.det h₁
  have e₂ := congrArg Matrix.det h₂
  rw [Matrix.det_mul, hd, hd, hd'] at e₁ e₂
  have hb : b.det ≠ 0 := fun h0 => hB' (by rw [e₁, h0, map_zero, mul_zero])
  have hu : m₁.det * m₂.det = 1 := Subtype.ext (mul_right_cancel₀ hB' (by
    rw [Subring.coe_mul, _root_.mul_assoc, ← e₂, ← e₁]; simp))
  have h₃ : (B * b⁻¹).map e = m₁.map (algebraMap _ (PadicAlgCl p)) := by
    rw [Matrix.map_mul, h₁, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hb.isUnit,
      Matrix.map_one _ (map_zero e) (map_one e), Matrix.mul_one]
  have h₄ : ∀ i k, ∃ a : u.V, u.j a = m₁ i k := fun i k => by
    have e' : e ((B * b⁻¹) i k) = (m₁ i k : OO p) := congrFun (congrFun h₃ i) k
    obtain ⟨a, ha⟩ := exists_of_eq_coe u e'
    exact ⟨a, Subtype.ext ((congrArg e ha).trans e')⟩
  choose m hm using h₄
  have h₅ : (Matrix.of m).map u.j = m₁ := Matrix.ext hm
  refine ⟨hb, Matrix.of m, ?_, ?_⟩
  · refine (isLocalHom_j u).map_nonunit _ ?_
    rw [RingHom.map_det, RingHom.mapMatrix_apply, h₅]
    exact IsUnit.of_mul_eq_one _ hu
  · rw [h₁, ← h₅]
    rfl

theorem exists_ptC (a : Sp (PadicAlgCl p) ⟶ u.G.left) (ha : a ≫ u.G.hom = gPt p ≫ spMap u.j) :
    ∃ a' : u.PtC, u.toG a' = a :=
  ⟨Over.homMk (pullback.lift a _ (ha.trans (gPt_j u))) (pullback.lift_snd _ _ _), pullback.lift_fst _ _ _⟩

theorem ptC_snd (a : u.PtC) : a.left ≫ pullback.snd u.G.hom (jK u.V) = jFK (R := u.V) (PadicAlgCl p) := Over.w a

theorem toG_over (a : u.PtC) : u.toG a ≫ u.G.hom = gPt p ≫ spMap u.j := by
  rw [gPt_j, ← ptC_snd u a, Category.assoc, ← pullback.condition]
  exact Category.assoc _ _ _

end Test

theorem exists_real_crd (h : ImmBy (baseOver (Sp S.R) ⊗ ρ.P.A).hom (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))) ρ.s
    Set.univ) {K : Type} [Field K] (a : Sp K ⟶ ρ.P.A.left) : ∃ v, v ≠ 0 ∧ ρ.Crd a v := by
  let a' : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left :=
    pullback.lift (f := 𝟙 (Sp S.R)) (a ≫ ρ.P.A.hom) a (Category.comp_id _)
  obtain ⟨v, hv⟩ := CrdCalc.crd_exists (H := LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R)))
    (DVR.linComb_isLB _ ρ.P.isLB _ _) ρ.s a'
  refine ⟨v, (ne_zero_iff hv).2 ?_, a', pullback.lift_snd _ _ _, hv⟩
  have := h.1
  simp only [Set.mem_univ, iSup_pos] at this
  rw [this]
  trivial

theorem big (ρ : S.Real) (h : S.Big) : Big S.g S.N (S.r * S.N) := by
  refine ⟨?_, h.1, h.2.1⟩
  have h1 := Nat.pow_le_pow_left (Nat.le_trans ρ.n_prime.two_le
    (Nat.le_self_pow (by have := ρ.two_le; omega : ρ.k ≠ 0) ρ.n)) 2
  rw [ρ.N_eq]
  omega

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]
  rfl

section Cover
variable {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (t : ρ.GeoTest p y₀)

theorem crd_generic [ArithBase o Ω] (hL : GlobalTheory.UT.LL) (hb : t.b.det ≠ 0) (a : Sp (PadicAlgCl p) ⟶ t.u.G.left)
    (ha : a ≫ t.u.G.hom = spMap ((OO p).subtype.comp t.u.j)) : ∃ w, w ≠ 0 ∧ Crd (t.u.H S.N) t.σ a w := by
  obtain ⟨a', h⟩ := exists_ptC t.u a (ha.trans (spMap_comp _ _))
  obtain ⟨v, hv, hc⟩ := exists_real_crd (GlobalTheory.ZH.ThetaSys.Real.immBy_basis hL o Ω S ρ) (t.u.toA a')
  have hd : (t.b.map (algebraMap _ (PadicAlgCl p))).det ≠ 0 := by
    have := (map_ne_zero (algebraMap _ (PadicAlgCl p))).2 hb
    rwa [RingHom.map_det] at this
  have h1 := t.link a' v hc
  rw [h] at h1
  exact ⟨_, fun h0 => hv (Matrix.eq_zero_of_mulVec_eq_zero hd h0), h1⟩

theorem crd_special (hL : GlobalTheory.UT.LL) (hS : S.Big) (a : Sp (kb p) ⟶ t.u.G.left)
    (ha : a ≫ t.u.G.hom = spMap ((IsLocalRing.residue (OO p)).comp t.u.j)) :
    ∃ w, w ≠ 0 ∧ Crd (t.u.H S.N) t.σ a w := by
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have pb : IsPullback t.mod.r t.mod.Φ.G.hom t.u.G.hom (rPt p ≫ spMap t.u.j) := t.mod.cart.1
  have hsq : a ≫ t.u.G.hom = 𝟙 _ ≫ rPt p ≫ spMap t.u.j :=
    (ha.trans (spMap_comp _ _)).trans (Category.id_comp _).symm
  let x : t.mod.Φ.Pt := Over.homMk (pb.lift a (𝟙 _) hsq) (pb.lift_snd _ _ hsq)
  have hx : x.left ≫ t.mod.r = a := pb.lift_fst _ _ hsq
  obtain ⟨v, hv⟩ := CrdCalc.crd_exists (R := kb p) (t.mod.Φ.H_isLB 1) t.mod.F x.left
  have h1 := t.mod.red x v hv
  rw [hx] at h1
  refine ⟨v, (ne_zero_iff hv).2 ?_, h1⟩
  have hcov := (GlobalTheory.T.immBy_weight_zero' hL.1 hL.2.1 (kb p) t.mod.Φ _ _ _ _ _ _ t.mod.F t.mod.pol (big ρ hS)
    t.mod.good t.mod.dim).1
  exact (hcov.ge.trans (iSup₂_le fun i _ => le_iSup (fun i => nonzeroLocus (t.mod.F i)) i)) trivial

theorem smooth : Smooth t.u.G.hom :=
  haveI := t.mod.smooth
  SmoothOfRelativeDimension.smooth S.g _

theorem iSup_comb_eq_top [ArithBase o Ω] (hL : GlobalTheory.UT.LL) (hS : S.Big) (hb : t.b.det ≠ 0)
    {m : Matrix S.J S.J t.u.V} (hm : IsUnit m.det) : ⨆ i, nonzeroLocus (comb t.u.G.hom t.σ (m i)) = ⊤ := by
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  haveI := smooth t
  haveI := isLocalHom_j t.u
  refine top_unique fun x _ => ?_
  by_cases hx : (t.u.G.hom x).asIdeal = ⊥
  · refine mem_iSup_comb hm _ (crd_generic t hL hb) ⟨IsLocalRing.closedPoint _, PrimeSpectrum.ext ?_⟩
    rw [hx]
    change Ideal.comap _ (IsLocalRing.maximalIdeal _) = _
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ (injective_j t.u)
  · refine mem_iSup_comb hm _ (crd_special t hL hS)
      ⟨IsLocalRing.closedPoint _, (IsLocalRing.comap_closedPoint
        ((IsLocalRing.residue (OO p)).comp t.u.j)).trans (PrimeSpectrum.ext ?_)⟩
    exact (IsLocalRing.eq_maximalIdeal
      (Ring.DimensionLEOne.maximalOfPrime hx (t.u.G.hom x).isPrime)).symm

end Cover

section Base
variable {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (Q : Clos ρ M U₀ EE)

theorem basis_mem_O (hE : S.IsEE M U₀ EE) (l : Q.Λ) {z : M.Z} (hz : z ∈ U₀) (hl : z ∈ Q.W l) (i j : S.J) :
    Q.B l i j ∈ M.O z := by
  have h : Q.B l i ∈ EE.E z := (Q.basis l z hl).ge (Submodule.subset_span ⟨i, rfl⟩)
  rw [hE.1 z hz] at h
  exact (RatModel.Lat.mem_const_iff M).1 h j

theorem val_c_mul (hE : S.IsEE M U₀ EE) (l : Q.Λ) {K : Type} [Field K] (x : Sp K ⟶ M.Z)
    (hz : x (IsLocalRing.closedPoint K) ∈ U₀) (hl : x (IsLocalRing.closedPoint K) ∈ Q.W l) :
    (Q.c l).map (valR x (Q.W l)) * (Q.B l).map (M.val x) = 1 := by
  have hr := RatModel.range_eq_singleton x (IsLocalRing.closedPoint K)
  generalize x (IsLocalRing.closedPoint K) = z at hz hl hr
  let cO : Matrix S.J S.J (M.O z) := fun i j => ⟨valF M.pt _ (Q.c l i j), RatModel.valF_mem_O hl _⟩
  let BO : Matrix S.J S.J (M.O z) := fun i j => ⟨Q.B l i j, basis_mem_O Q hE l hz hl i j⟩
  have h : cO * BO = 1 := by
    refine Matrix.map_injective (f := (M.O z).val.toRingHom) Subtype.val_injective ?_
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Q.c_inv l
  have h2 := congrArg (fun A => A.map (RatModel.valHom x z hr)) h
  beta_reduce at h2
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  rw [← h2]
  congr 1
  exact Matrix.ext fun i j => (RatModel.val_valF (hr.le.trans (Set.singleton_subset_iff.2 hl)) _).symm

theorem span_val (hE : S.IsEE M U₀ EE) (l : Q.Λ) {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z)
    (hz : (gPt p ≫ y) (IsLocalRing.closedPoint _) ∈ U₀) (hl : y (cPt p) ∈ Q.W l) :
    Submodule.span (OO p) ((fun (v : S.J → Ω) j => M.val (gPt p ≫ y) (v j)) '' (EE.E (y (cPt p)))) =
      Submodule.span (OO p) (Set.range ((Q.B l).map (M.val (gPt p ≫ y)))) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨v, hv, rfl⟩
    have hs := RatModel.gPt_specializes (y := y) rfl (IsLocalRing.closedPoint _)
    have hr := RatModel.range_eq_singleton (gPt p ≫ y) (IsLocalRing.closedPoint _)
    generalize (gPt p ≫ y) (IsLocalRing.closedPoint _) = z at hz hs hr
    rw [Q.basis l _ hl] at hv
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
    refine (Submodule.mem_span_range_iff_exists_fun _).2
      ⟨fun i => RatModel.valLoc y _ specializes_rfl (a i), funext fun j => ?_⟩
    let BO : S.J → M.O z := fun i => ⟨Q.B l i j, basis_mem_O Q hE l hz (hs.mem_open (Q.W l).isOpen hl) i j⟩
    let aO : S.J → M.O z := fun i => ⟨a i, RatModel.O_le_of_specializes hs (a i).2⟩
    have e : (∑ i, a i • Q.B l i) j = ((∑ i, aO i * BO i : M.O z) : Ω) := by
      simp [aO, BO, Finset.sum_apply, Subalgebra.smul_def]
    beta_reduce
    rw [e, ← RatModel.valHom_apply _ z hr, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, RatModel.valHom_apply, RatModel.valHom_apply]
    exact congrArg (· * _) (RatModel.val_gPt rfl (a i)).symm
  · rintro _ ⟨i, rfl⟩
    exact ⟨Q.B l i, (Q.basis l _ hl).ge (Submodule.subset_span ⟨i, rfl⟩), rfl⟩

variable {Q} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p} {t : ρ.GeoTest p y₀}
  (c : Q.Fac y t.u)

theorem gPt_eq : gPt p ≫ y = jFK (R := t.u.V) (PadicAlgCl p) ≫ c.yK ≫ U₀.ι := by
  rw [c.yK_fac, ← Category.assoc, ← gPt_j, Category.assoc, c.fac]

include c in
theorem gPt_mem (w) : (gPt p ≫ y) w ∈ U₀ := by
  rw [gPt_eq c, ← Category.assoc, Scheme.Hom.comp_apply]
  exact Subtype.prop _

theorem le_preimage_yV {W : M.Z.Opens} (h : y (cPt p) ∈ W) : ⊤ ≤ c.yV ⁻¹ᵁ W := by
  haveI := isLocalHom_j t.u
  refine (CrdCalc.top_le_iff _ _).2 ?_
  rw [← c.fac, Scheme.Hom.comp_apply] at h
  exact (IsLocalRing.comap_closedPoint t.u.j) ▸ h

include c in
theorem exists_change (hE : S.IsEE M U₀ EE) {l : Q.Λ} (hl : y (cPt p) ∈ Q.W l) :
    t.b.det ≠ 0 ∧ ∃ m : Matrix S.J S.J t.u.V, IsUnit m.det ∧ (Q.B l).map (M.val (gPt p ≫ y)) =
      (m.map fun a => (t.u.j a : PadicAlgCl p)) * t.b.map (algebraMap _ (PadicAlgCl p)) := by
  let x : Sp (FractionRing t.u.V) ⟶ M.Z := c.yK ≫ U₀.ι
  have hz : x (IsLocalRing.closedPoint _) ∈ U₀ := Subtype.prop (c.yK _)
  have hx : x (IsLocalRing.closedPoint _) ∈ Q.W l := by
    rw [show x = _ from c.yK_fac]
    exact le_preimage_yV c hl (x := jK t.u.V _) trivial
  have e : ((Q.B l).map (M.val x)).map (algebraMap _ (PadicAlgCl p)) = (Q.B l).map (M.val (gPt p ≫ y)) := by
    refine Matrix.ext fun i j => ?_
    have := RatModel.val_spMap_comp (algebraMap _ (PadicAlgCl p)) x specializes_rfl
      ⟨_, basis_mem_O Q hE l hz hx i j⟩
    rw [RatModel.valLoc_eq_val] at this
    rw [gPt_eq c]
    exact this.symm
  rw [← e]
  refine exists_matrix t.u (Matrix.det_ne_zero_of_left_inverse (val_c_mul Q hE l x hz hx)) ?_
  rw [e, ← span_val Q hE l y (gPt_mem c _) hl, ← t.span]
  exact hE.2 _ p y y₀ t.τ ⟨rfl, by rintro _ ⟨w, rfl⟩; exact gPt_mem c w⟩ c.at_

end Base

section Main
variable {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} {Q : Clos ρ M U₀ EE}
  {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p} {t : ρ.GeoTest p y₀}
  (c : Q.Fac y t.u)

noncomputable def genMap : pullback t.u.G.hom (jK t.u.V) ⟶ pullback ρ.P.A.hom Q.u₀ :=
  pullback.lift (t.u.U.gen.hom.left ≫ t.u.φ) (pullback.snd _ _ ≫ c.yK) (by
    have h1 : t.u.φ ≫ ρ.P.A.hom = t.u.A.A.hom ≫ spMap t.u.yK := t.u.cart.1.w
    have h2 : t.u.U.gen.hom.left ≫ t.u.A.A.hom = pullback.snd t.u.G.hom (jK t.u.V) := Over.w _
    rw [Category.assoc, Category.assoc, c.yK_u, h1, ← h2]
    exact (Category.assoc _ _ _).symm)

theorem genMap_fst : genMap c ≫ pullback.fst _ _ = t.u.U.gen.hom.left ≫ t.u.φ := pullback.lift_fst _ _ _

theorem genMap_snd : genMap c ≫ pullback.snd _ _ = pullback.snd _ _ ≫ c.yK := pullback.lift_snd _ _ _

theorem genMap_over : (genMap c ≫ Q.a₀) ≫ Q.P.hom = pullback.snd _ _ ≫ c.yK ≫ U₀.ι := by
  rw [Category.assoc, Q.cart.w, ← Category.assoc, genMap_snd, Category.assoc]

noncomputable def ptA (a : t.u.PtC) : Sp (PadicAlgCl p) ⟶ pullback ρ.P.A.hom Q.u₀ := a.left ≫ genMap c

theorem ptA_fst (a : t.u.PtC) : ptA c a ≫ pullback.fst _ _ = t.u.toA a :=
  (Category.assoc _ _ _).trans (congrArg (a.left ≫ ·) (genMap_fst c))

theorem ptA_over (a : t.u.PtC) : (ptA c a ≫ Q.a₀) ≫ Q.P.hom = gPt p ≫ y := by
  rw [gPt_eq c, ← ptC_snd t.u a, Category.assoc a.left, ← genMap_over]
  simp only [ptA, Category.assoc]

theorem crd_match [ArithBase o Ω] (hL : GlobalTheory.UT.LL) (hE : S.IsEE M U₀ EE) {l : Q.Λ} (hl : y (cPt p) ∈ Q.W l)
    {m : Matrix S.J S.J t.u.V} (hm : (Q.B l).map (M.val (gPt p ≫ y)) =
      (m.map fun a => (t.u.j a : PadicAlgCl p)) * t.b.map (algebraMap _ (PadicAlgCl p)))
    (a : t.u.PtC) (x : Sp (PadicAlgCl p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme)
    (hx : x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι = ptA c a ≫ Q.a₀) :
    ∃ v, Crd (t.u.H S.N) (fun i => comb t.u.G.hom t.σ (m i)) (t.u.toG a) v ∧
      Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x v := by
  obtain ⟨v, -, hv⟩ := exists_real_crd (GlobalTheory.ZH.ThetaSys.Real.immBy_basis hL o Ω S ρ) (t.u.toA a)
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists (pull_isLB Q.isLB (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x
  have h1 := Q.rel l _ x w hw
  rw [← Category.assoc, hx, ptA_over] at h1
  have h2 := Q.crd _ (ptA c a) v (by rw [ptA_fst]; exact hv)
  obtain ⟨e, he⟩ := CrdCalc.crd_unique h2 h1
  have h3 := crd_comb m ((toG_over t.u a).trans (spMap_comp _ _).symm) (t.link a v hv)
  refine ⟨w, ?_, hw⟩
  have h4 := mul_eq_one_comm.1 (val_c_mul Q hE l (gPt p ≫ y) (gPt_mem c _)
    ((RatModel.gPt_specializes (y := y) rfl _).mem_open (Q.W l).isOpen hl))
  have h5 : ((Q.c l).map (valR (gPt p ≫ y) (Q.W l))).mulVec w = (e : PadicAlgCl p) • v := funext he
  have h6 : w = (e : PadicAlgCl p) • ((Q.B l).map (M.val (gPt p ≫ y))).mulVec v := by
    rw [← Matrix.mulVec_smul, ← h5, Matrix.mulVec_mulVec, h4, Matrix.one_mulVec]
  rw [h6, hm, ← Matrix.mulVec_mulVec]
  exact CrdCalc.crd_smul e h3

theorem dense_toG : Dense (⋃ a : t.u.PtC, Set.range (t.u.toG a)) := by
  haveI := smooth t
  refine (dense_pts t.u.G.hom _ (denseRange_spMap (injective_j t.u))).mono (Set.iUnion_subset fun a => ?_)
  obtain ⟨a', h⟩ := exists_ptC t.u a.1 (a.2.trans (spMap_comp _ _))
  exact h ▸ Set.subset_iUnion (fun a : t.u.PtC => Set.range (t.u.toG a)) a'

end Main

theorem nonempty_tMap : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u), S.Big → Nonempty (Q.TMap t c) := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q p _ y y₀ t c hS
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 (Q.cover.ge (Set.mem_univ (y (cPt p))))
  obtain ⟨hb, m, hm, hme⟩ := exists_change c hB.ee hl
  haveI := smooth t
  haveI : IsReduced t.u.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced t.u.G.hom
  obtain ⟨yW, hyW⟩ : ∃ yW : Sp t.u.V ⟶ (Q.W l).toScheme, yW ≫ (Q.W l).ι = c.yV :=
    ⟨IsOpenImmersion.lift _ _ (by
      rw [Scheme.Opens.range_ι]
      exact (top_le_preimage_iff _ _).1 (le_preimage_yV c hl)), IsOpenImmersion.lift_fac _ _ _⟩
  have hx : ∀ a : t.u.PtC, ∃ x : Sp (PadicAlgCl p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme,
      x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι = ptA c a ≫ Q.a₀ := fun a =>
    ⟨IsOpenImmersion.lift _ _ (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      change Q.P.hom _ ∈ Q.W l
      rw [← Scheme.Hom.comp_apply, ptA_over]
      exact (RatModel.gPt_specializes (y := y) rfl _).mem_open (Q.W l).isOpen hl),
      IsOpenImmersion.lift_fac _ _ _⟩
  choose x hx using hx
  obtain ⟨f, hf, hfx, hfc⟩ := GlobalTheory.T.exists_factor_closedImmersion_dense_points Γ(M.Z, Q.W l) _ t.u.G.left ((Q.P.hom ∣_ Q.W l) ≫ (Q.aff l).isoSpec.hom)
    ((t.u.G.hom ≫ yW) ≫ (Q.aff l).isoSpec.hom) _ (t.u.H S.N) S.J (Q.σ l) (fun i => comb t.u.G.hom t.σ (m i))
    (pull_isLB Q.isLB _) t.mod.isLB (Q.imm l) (iSup_comb_eq_top t hL hS hb hm) (PadicAlgCl p) t.u.PtC t.u.toG x
    dense_toG (fun a => ⟨by
      have : x a ≫ (Q.P.hom ∣_ Q.W l) = t.u.toG a ≫ t.u.G.hom ≫ yW := by
        rw [← cancel_mono (Q.W l).ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hx, ptA_over,
          Category.assoc, Category.assoc, hyW, ← Category.assoc, toG_over, Category.assoc, c.fac]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (Q.aff l).isoSpec.hom) this).trans
        (Category.assoc _ _ _)), crd_match c hL hB.ee hl hme a _ (hx a)⟩)
  have hf' : f ≫ (Q.P.hom ∣_ Q.W l) = t.u.G.hom ≫ yW :=
    (cancel_mono (Q.aff l).isoSpec.hom).1 ((Category.assoc _ _ _).trans hf)
  have hover : f ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = t.u.G.hom ≫ c.yV := by
    rw [← morphismRestrict_ι, ← Category.assoc, hf', Category.assoc, hyW]
  refine ⟨⟨l, hl, m, hm, hme, f, hover, genMap c, genMap_fst c, genMap_snd c, ?_,
    fun R _ _ ψ z w hz hw => hfc R z _ (crd_comb m hz hw)⟩⟩
  haveI := Q.proper
  haveI : IsReduced (pullback t.u.G.hom (jK t.u.V)) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd _ _)
  refine ext_of_pts Q.P.hom ?_ _ (dense_pts (pullback.snd t.u.G.hom (jK t.u.V)) _
    (denseRange_spMap (algebraMap _ (PadicAlgCl p)).injective)) fun a => ?_
  · rw [genMap_over, c.yK_fac, Category.assoc, Category.assoc, hover, pullback.condition_assoc]
  · let a' : t.u.PtC := Over.homMk a.1 a.2
    have h1 : (a.1 ≫ pullback.fst _ _) ≫ f = x a' := hfx a'
    have h2 : x a' ≫ _ = (a.1 ≫ genMap c) ≫ Q.a₀ := hx a'
    rw [← Category.assoc, ← h2, ← h1, Category.assoc, Category.assoc]

end GlobalTheory.ZH.TestMap
