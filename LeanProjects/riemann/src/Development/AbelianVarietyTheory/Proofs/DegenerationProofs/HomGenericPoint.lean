import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.InFibChart

theorem eval_scale {K J : Type} [CommRing K] (c : K) (x : J → K) {F : MvPolynomial J K} {d : ℕ}
    (hF : F.IsHomogeneous d) :
    MvPolynomial.eval (fun j => c * x j) F = c ^ d * MvPolynomial.eval x F := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i ∈ m.support, m i = d := by
    have := hF (MvPolynomial.mem_support_iff.1 hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem exists_subst {K J : Type} [CommRing K] [Fintype J] (g : Matrix J J K) {F : MvPolynomial J K} {d : ℕ}
    (hF : F.IsHomogeneous d) :
    ∃ F' : MvPolynomial J K, F'.IsHomogeneous d ∧
      ∀ v, MvPolynomial.eval v F' = MvPolynomial.eval (g.mulVec v) F := by
  refine ⟨MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (g i j) * MvPolynomial.X j) F, ?_, fun v => ?_⟩
  · have := hF.aeval (n := 1) (fun i => ∑ j, MvPolynomial.C (g i j) * (MvPolynomial.X j : MvPolynomial J K))
      (fun i => MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => MvPolynomial.isHomogeneous_C_mul_X _ _)
    simpa using this
  · clear hF
    induction F using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, hp]
      simp [Matrix.mulVec, dotProduct]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J} (Q : Clos ρ M U₀ EE)

theorem hom_genericPoint (hU : (U₀ : Set M.Z).Nonempty) :
    Q.P.hom (genericPoint Q.P.left) = genericPoint M.Z := by
  have hg : genericPoint M.Z ∈ U₀ := (genericPoint_specializes hU.some).mem_open U₀.isOpen hU.some_mem
  have hw : η[ρ.P.A].left ≫ ρ.P.A.hom = 𝟙 _ := Over.w η[ρ.P.A]
  let s : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀ :=
    pullback.lift (Q.u₀ ≫ η[ρ.P.A].left) (𝟙 _) (by
      rw [Category.assoc, Category.id_comp]; exact (congrArg (Q.u₀ ≫ ·) hw).trans (Category.comp_id _))
  have hs : (s ≫ Q.a₀) ≫ Q.P.hom = U₀.ι := by
    rw [Category.assoc, Q.cart.w, pullback.lift_snd_assoc, Category.id_comp]
  have h1 : Q.P.hom ((s ≫ Q.a₀) ⟨_, hg⟩) = genericPoint M.Z :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun f : U₀.toScheme ⟶ M.Z => f ⟨_, hg⟩) hs)
  have h2 := (genericPoint_specializes ((s ≫ Q.a₀) ⟨_, hg⟩)).map Q.P.hom.continuous
  rw [h1] at h2
  exact (h2.antisymm (genericPoint_specializes _)).eq

theorem exists_change (l l' : Q.Λ) {z : M.Z} (hl : z ∈ Q.W l) (hl' : z ∈ Q.W l') :
    ∃ g : Matrix S.J S.J (M.O z), Q.B l' = g.map (↑) * Q.B l ∧
      (Q.c l).map (valF M.pt (Q.W l)) = (Q.c l').map (valF M.pt (Q.W l')) * g.map (↑) := by
  have h : ∀ i, ∃ a : S.J → M.O z, ∑ j, a j • Q.B l j = Q.B l' i := fun i => by
    refine (Submodule.mem_span_range_iff_exists_fun (M.O z) (v := fun j k => Q.B l j k)).1 ?_
    refine (Q.basis l z hl).le ((Q.basis l' z hl').ge ?_)
    exact Submodule.subset_span ⟨i, rfl⟩
  choose a ha using h
  have e : Q.B l' = (Matrix.of a).map (↑) * Q.B l := by
    ext i k
    rw [← ha i]
    simp [Matrix.mul_apply, Finset.sum_apply, Subalgebra.smul_def]
  refine ⟨Matrix.of a, e, ?_⟩
  have h1 := mul_eq_one_comm.1 (Q.c_inv l)
  have h2 := Q.c_inv l'
  rw [e] at h2
  calc _ = ((Q.c l').map (valF M.pt (Q.W l')) * ((Matrix.of a).map (↑) * Q.B l)) *
        (Q.c l).map (valF M.pt (Q.W l)) := by rw [h2, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem crd_change_loc (l l' : Q.Λ) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (y : Sp R ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (y' : Sp R ⟶ (Q.P.hom ⁻¹ᵁ Q.W l').toScheme) (t : Sp R ⟶ M.Z)
    (hy : y' ≫ (Q.P.hom ⁻¹ᵁ Q.W l').ι = y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι)
    (ht : y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = t) (q : Sp R) (hq : t q = genericPoint M.Z)
    {z : M.Z} (hz : t (IsLocalRing.closedPoint R) ⤳ z) (hl : z ∈ Q.W l) (hl' : z ∈ Q.W l')
    (g : Matrix S.J S.J (M.O z))
    (hg : (Q.c l).map (valF M.pt (Q.W l)) = (Q.c l').map (valF M.pt (Q.W l')) * g.map (↑))
    {w w' : S.J → R} (hw : Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) y w)
    (hw' : Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l').ι) (Q.σ l') y' w') :
    ∃ u : Rˣ, ∀ j, w' j = (u : R) * (g.map (RatModel.valLoc t z hz)).mulVec w j := by
  have ht' : y' ≫ (Q.P.hom ⁻¹ᵁ Q.W l').ι ≫ Q.P.hom = t := by
    rw [← Category.assoc, hy, Category.assoc, ht]
  have h1 := Q.rel l R y w hw
  have h2 := Q.rel l' R y' w' hw'
  rw [ht] at h1
  rw [ht', hy] at h2
  obtain ⟨u, hu⟩ := CrdCalc.crd_unique h1 h2
  refine ⟨u, ?_⟩
  let C : Matrix S.J S.J (M.O z) := Matrix.of fun i j => ⟨_, RatModel.valF_mem_O hl (Q.c l i j)⟩
  let C' : Matrix S.J S.J (M.O z) := Matrix.of fun i j => ⟨_, RatModel.valF_mem_O hl' (Q.c l' i j)⟩
  have hC : C = C' * g := by
    ext i j
    have := congrFun (congrFun hg i) j
    simpa [Matrix.mul_apply, C, C'] using this
  have e1 : (Q.c l).map (valR t (Q.W l)) = C.map (RatModel.valLoc t z hz) := by
    ext i j
    exact (RatModel.valLoc_valF t hz hl _).symm
  have e2 : (Q.c l').map (valR t (Q.W l')) = C'.map (RatModel.valLoc t z hz) := by
    ext i j
    exact (RatModel.valLoc_valF t hz hl' _).symm
  have hW : ⊤ ≤ t ⁻¹ᵁ Q.W l' := (CrdCalc.top_le_iff t _).2 (hz.mem_open (Q.W l').isOpen hl')
  have hdet : ((Q.c l').map (valR t (Q.W l'))).det ≠ 0 := by
    have e3 : (Q.c l').map (valR t (Q.W l')) = (CrdCalc.valHom t _ hW).mapMatrix (Q.c l') := by
      ext i j
      exact CrdCalc.valR_eq t _ hW _
    rw [e3, ← RingHom.map_det]
    intro h0
    have hpt : ⊤ ≤ M.pt ⁻¹ᵁ Q.W l' := M.top_le_preimage_pt (Q.ne l')
    have e4 : (Q.c l').map (valF M.pt (Q.W l')) = (CrdCalc.valHom M.pt _ hpt).mapMatrix (Q.c l') := by
      ext i j
      exact CrdCalc.valR_eq M.pt _ hpt _
    have h5 : IsUnit (valR M.pt (Q.W l') (Q.c l').det) := by
      rw [CrdCalc.valR_eq M.pt _ hpt, RingHom.map_det, ← e4]
      exact Matrix.isUnit_det_of_right_inverse (Q.c_inv l')
    have h6 : genericPoint M.Z ∈ M.Z.basicOpen (Q.c l').det := by
      rw [← M.pt_apply (IsLocalRing.closedPoint Ω)]
      exact (CrdCalc.isUnit_valR_iff M.pt _ hpt _).1 h5 (Set.mem_univ _)
    have h7 : (t.appLE (Q.W l') ⊤ hW).hom (Q.c l').det = 0 :=
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective (h0.trans (map_zero _).symm)
    have b := Scheme.basicOpen_appLE t ⊤ (Q.W l') hW (Q.c l').det
    have h8 : q ∈ (Sp R).basicOpen ((t.appLE (Q.W l') ⊤ hW).hom (Q.c l').det) :=
      b.ge ⟨trivial, show t q ∈ _ from hq ▸ h6⟩
    rw [h7, Scheme.basicOpen_zero] at h8
    exact h8
  have h9 : ((Q.c l').map (valR t (Q.W l'))).mulVec
      (w' - (u : R) • (g.map (RatModel.valLoc t z hz)).mulVec w) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, sub_eq_zero]
    funext j
    rw [hu j, e1, e2, hC, Matrix.map_mul]
    rfl
  have h10 := sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero hdet h9)
  intro j
  rw [h10]
  rfl

theorem crd_change (hU : (U₀ : Set M.Z).Nonempty) (l l' : Q.Λ) {K : Type} [Field K]
    (x : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (x' : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l').toScheme) (t : Sp K ⟶ M.Z)
    (hx : x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l').ι = x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι)
    (ht : x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = t)
    {z : M.Z} (hz : t (IsLocalRing.closedPoint K) = z) (hl : z ∈ Q.W l) (hl' : z ∈ Q.W l')
    (g : Matrix S.J S.J (M.O z))
    (hg : (Q.c l).map (valF M.pt (Q.W l)) = (Q.c l').map (valF M.pt (Q.W l')) * g.map (↑))
    {w w' : S.J → K} (hw : Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x w)
    (hw' : Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l').ι) (Q.σ l') x' w') :
    ∃ u : K, w' = fun j => u * (g.map fun a => M.val t a).mulVec w j := by
  obtain ⟨X, hX⟩ : ∃ X : Sp K ⟶ Q.P.left, X = x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι := ⟨_, rfl⟩
  have hXt : X ≫ Q.P.hom = t := by rw [hX, Category.assoc, ht]
  let p : Q.P.left := X (IsLocalRing.closedPoint K)
  have hp : Q.P.hom p = z := by
    rw [← hz, ← hXt]
    exact (Scheme.Hom.comp_apply _ _ _).symm
  let R : Type := Q.P.left.presheaf.stalk p
  let Y : Sp R ⟶ Q.P.left := Q.P.left.fromSpecStalk p
  let φ : R →+* K := (Scheme.stalkClosedPointTo (R := .of K) X).hom
  have hφ : spMap φ ≫ Y = X := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of K) X
  have hr : Set.range Y = {ξ | ξ ⤳ p} := Scheme.range_fromSpecStalk
  have hlift : ∀ k : Q.Λ, z ∈ Q.W k → ∃ y : Sp R ⟶ (Q.P.hom ⁻¹ᵁ Q.W k).toScheme,
      y ≫ (Q.P.hom ⁻¹ᵁ Q.W k).ι = Y := fun k hk =>
    ⟨IsOpenImmersion.lift _ Y (by
      rw [Scheme.Opens.range_ι, hr]
      exact fun ξ hξ => Specializes.mem_open hξ (Q.P.hom ⁻¹ᵁ Q.W k).isOpen (show Q.P.hom p ∈ Q.W k from hp ▸ hk)),
      IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨y, hy⟩ := hlift l hl
  obtain ⟨y', hy'⟩ := hlift l' hl'
  have hxy : spMap φ ≫ y = x := by
    rw [← cancel_mono (Q.P.hom ⁻¹ᵁ Q.W l).ι, Category.assoc, hy, hφ, hX]
  have hxy' : spMap φ ≫ y' = x' := by
    rw [← cancel_mono (Q.P.hom ⁻¹ᵁ Q.W l').ι, Category.assoc, hy', hφ, hX, hx]
  obtain ⟨q, hq⟩ : genericPoint Q.P.left ∈ Set.range Y := hr ▸ genericPoint_specializes p
  have hq' : (Y ≫ Q.P.hom) q = genericPoint M.Z := by
    rw [Scheme.Hom.comp_apply, hq, hom_genericPoint Q hU]
  have hc : (Y ≫ Q.P.hom) (IsLocalRing.closedPoint R) ⤳ z := by
    have : Y (IsLocalRing.closedPoint R) = p := Scheme.fromSpecStalk_closedPoint
    exact specializes_of_eq ((Scheme.Hom.comp_apply _ _ _).trans ((congrArg Q.P.hom this).trans hp))
  obtain ⟨v, hv⟩ := CrdCalc.crd_exists (LB.isLB_pull Q.isLB _) (Q.σ l) y
  obtain ⟨v', hv'⟩ := CrdCalc.crd_exists (LB.isLB_pull Q.isLB _) (Q.σ l') y'
  obtain ⟨u, hu⟩ := crd_change_loc Q l l' y y' (Y ≫ Q.P.hom) (hy'.trans hy.symm)
    (by rw [← Category.assoc, hy]) q hq' hc hl hl' g hg hv hv'
  have k1 := CrdCalc.crd_map φ hv
  have k2 := CrdCalc.crd_map φ hv'
  rw [hxy] at k1
  rw [hxy'] at k2
  obtain ⟨a, ha⟩ := CrdCalc.crd_unique hw k1
  obtain ⟨b, hb⟩ := CrdCalc.crd_unique k2 hw'
  refine ⟨b * φ u * a, funext fun j => ?_⟩
  have hval : ∀ c : M.O z, φ (RatModel.valLoc (Y ≫ Q.P.hom) z hc c) = M.val t c := fun c => by
    rw [← RatModel.val_spMap_comp, ← Category.assoc, hφ, hXt]
  rw [hb j]
  simp only [hu j, map_mul, Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply, hval, ha, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem tors_change (hB : BaseFacts S M U₀ EE) (l l' : Q.Λ) {K : Type} [Field K] (t : Sp K ⟶ M.Z)
    {z : M.Z} (hz : t (IsLocalRing.closedPoint K) = z) (hl : z ∈ Q.W l)
    (g : Matrix S.J S.J (M.O z)) (hg : Q.B l' = g.map (↑) * Q.B l) {v : S.J → K} (hv : v ∈ Q.Tors t l) :
    (g.map fun a => M.val t a).mulVec v ∈ Q.Tors t l' := by
  obtain ⟨z', ⟨w, hw⟩, x₀, hx₀, h, hh, rfl⟩ := hv
  have hzz : z' = z := by rw [← hw, ← hz, Subsingleton.elim w (IsLocalRing.closedPoint K)]
  subst hzz
  refine ⟨z', ⟨w, hw⟩, x₀, hx₀, h, hh, funext fun i => ?_⟩
  have hr : Set.range t = {z'} := hw ▸ RatModel.range_eq_singleton t w
  let a : S.J → M.O z' := fun j => ⟨(Q.B l j ⬝ᵥ S.ev h) / S.th x₀,
    (hB.sec z' x₀ hx₀ h hh).1 _ ((Q.basis l z' hl).ge (Submodule.subset_span ⟨j, rfl⟩))⟩
  have e : (Q.B l' i ⬝ᵥ S.ev h) / S.th x₀ = ((∑ j, g i j * a j : M.O z') : Ω) := by
    have e1 : Q.B l' i ⬝ᵥ S.ev h = (Q.B l').mulVec (S.ev h) i := rfl
    rw [e1, hg, ← Matrix.mulVec_mulVec]
    simp [a, Matrix.mulVec, dotProduct, Finset.sum_div, mul_div_assoc]
  rw [e, ← RatModel.valHom_apply t z' hr, map_sum]
  simp only [map_mul, RatModel.valHom_apply]
  rfl

theorem inFib_of_chart : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (K : Type) [Field K] (l : Q.Λ) (x' : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (w : S.J → K), Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x' w → (∀ (d : ℕ) (Pf : MvPolynomial S.J K), d ≤ S.N ^ S.g * S.g.factorial → Pf.IsHomogeneous d → (∀ v ∈ Q.Tors (x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) l, MvPolynomial.eval v Pf = 0) → MvPolynomial.eval w Pf = 0) → Q.InFib (x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) := by
  intro o Ω _ _ _ _ S ρ M U₀ EE hB Q K _ l x w hw H l' x' w' hx hw' d Pf hd hPf hT
  rw [Category.assoc] at hT
  obtain ⟨t, ht⟩ : ∃ t, x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = t := ⟨_, rfl⟩
  have ht' : x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l').ι ≫ Q.P.hom = t := by rw [← Category.assoc, hx, Category.assoc, ht]
  rw [ht] at hT H
  have hl : t (IsLocalRing.closedPoint K) ∈ Q.W l := by
    rw [← ht]
    exact (x (IsLocalRing.closedPoint K)).2
  have hl' : t (IsLocalRing.closedPoint K) ∈ Q.W l' := by
    rw [← ht']
    exact (x' (IsLocalRing.closedPoint K)).2
  obtain ⟨g, hg, hc⟩ := exists_change Q l l' hl hl'
  obtain ⟨u, rfl⟩ := crd_change Q hB.ov.ne l l' x x' t hx ht rfl hl hl' g hc hw hw'
  obtain ⟨F, hF, hev⟩ := exists_subst (g.map fun a => M.val t a) hPf
  have h0 := H d F hd hF fun v hv => by
    rw [hev]
    exact hT _ (tors_change Q hB l l' t rfl hl g hg hv)
  rw [eval_scale u _ hPf, ← hev, h0, mul_zero]

end GlobalTheory.ZH.InFibChart
end
