import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdNeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPullDeg

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace FamIntAt

theorem exists_extend {X Y Z : Scheme.{0}} [IsReduced Y] {L : LB X} (hL : L.IsLB) (ζ : Z ⟶ Y) (ξ : Z)
    (hξ : ∀ z : Z, z = ξ) (hd : ∀ U : Y.Opens, U ≠ ⊥ → ζ ξ ∈ U) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (t : LB.Sec (LB.LinComb L (fun k => ζ ≫ φ k) ε))
    (H : ∀ q : Y, ∃ (j : K → L.ι) (V : Y.Opens) (a : Γ(Y, V)), q ∈ V ∧ V ≤ LB.wchart L φ j ∧
      gs ζ ξ V a = gs (𝟙 Z) ξ (LB.wchart L (fun k => ζ ≫ φ k) j) (t.f j)) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (T : Scheme.{0}) (r : T ⟶ Z) (z : T) (J), Good L z J →
      sval s (r ≫ ζ) z J = sval t r z J := by
  have inj : ∀ (V : Y.Opens) (a b : Γ(Y, V)), (ζ ξ ∈ V → gs ζ ξ V a = gs ζ ξ V b) → a = b := by
    intro V a b h
    by_cases hV : V = ⊥
    · exact fn_ext fun x hx => (hV.le hx : x ∈ (⊥ : Y.Opens)).elim
    · exact PsiInPull.gs_injective ζ ξ hd V (hd V hV) (h (hd V hV))
  have mem : ∀ {j : K → L.ι} {z : Z}, ζ z ∈ LB.wchart L φ j → (𝟙 Z : Z ⟶ Z) z ∈ LB.wchart L (fun k => ζ ≫ φ k) j :=
    fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 h k
  have tr : ∀ {j j' : K → L.ι}, ζ ξ ∈ LB.wchart L φ j → ζ ξ ∈ LB.wchart L φ j' →
      gs (𝟙 Z) ξ (LB.wchart L (fun k => ζ ≫ φ k) j) (t.f j) =
        gs ζ ξ (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j').val *
          gs (𝟙 Z) ξ (LB.wchart L (fun k => ζ ≫ φ k) j') (t.f j') := fun {j j'} h h' => by
    refine (sec_trans t (𝟙 Z) ξ (mem h) (mem h')).trans (congrArg₂ (· * ·) (Eq.symm ?_) rfl)
    refine (gs_unit ζ ξ _ (show ζ ξ ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' from ⟨h, h'⟩) _).trans
      (congrArg Units.val ((gm_linComb L φ ε ζ ξ j j' h h').trans ?_))
    simp only [trF, Category.id_comp]
  choose j₀ V a hq hV ha using H
  have glue : ∀ j : K → L.ι, ∃ b : Γ(Y, LB.wchart L φ j), ζ ξ ∈ LB.wchart L φ j →
      gs ζ ξ _ b = gs (𝟙 Z) ξ (LB.wchart L (fun k => ζ ≫ φ k) j) (t.f j) := by
    intro j
    let W : Y → Y.Opens := fun q => LB.wchart L φ j ⊓ V q
    have l : ∀ q, W q ≤ LB.wchart L φ j ⊓ LB.wchart L φ (j₀ q) := fun q => inf_le_inf_left _ (hV q)
    obtain ⟨u, hu⟩ : ∃ u : ∀ q, Γ(Y, W q), ∀ q, ζ ξ ∈ W q →
        gs ζ ξ (W q) (u q) = gs (𝟙 Z) ξ (LB.wchart L (fun k => ζ ≫ φ k) j) (t.f j) :=
      ⟨fun q => (Y.presheaf.map (homOfLE (l q)).op).hom ((LB.LinComb L φ ε).g j (j₀ q)).val *
          (Y.presheaf.map (homOfLE (inf_le_right : W q ≤ V q)).op).hom (a q), fun q h =>
        (gs_mul ζ ξ _ h _ _).trans ((congrArg₂ (· * ·) (gs_res ζ ξ (l q) h _)
          ((gs_res ζ ξ inf_le_right h _).trans (ha q))).trans (tr h.1 (hV q h.2)).symm)⟩
    obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L φ j)
      (fun q => homOfLE inf_le_left) (fun y hy => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy, hq y⟩) u
      (fun q q' => inj (W q ⊓ W q') _ _ fun h =>
        (gs_res ζ ξ inf_le_left h _).trans ((hu q h.1).trans ((hu q' h.2).symm.trans
          (gs_res ζ ξ inf_le_right h _).symm)))
    refine ⟨b, fun h => ?_⟩
    have hz : ζ ξ ∈ W (ζ ξ) := ⟨h, hq _⟩
    exact (gs_res ζ ξ inf_le_left hz b).symm.trans ((congrArg (gs ζ ξ (W (ζ ξ))) (hb _)).trans (hu _ hz))
  choose b hb using glue
  refine ⟨⟨b, fun j j' => inj _ _ _ fun h => ?_⟩, fun T r z J hJ => ?_⟩
  · exact (gs_res ζ ξ _ h _).trans ((hb j h.1).trans ((tr h.1 h.2).trans (Eq.symm ((gs_mul ζ ξ _ h _ _).trans
      (congrArg₂ (· * ·) rfl ((gs_res ζ ξ _ h _).trans (hb j' h.2)))))))
  · rw [sval_of _ (r ≫ ζ) z J (fun k => J (r ≫ ζ ≫ φ k)) (fun k => by rw [Category.assoc])]
    have hm := hJ.mem (fun k => ζ ≫ φ k) r
    have le : LB.wchart L (fun k => ζ ≫ φ k) (fun k => J (r ≫ ζ ≫ φ k)) ≤
        ζ ⁻¹ᵁ LB.wchart L φ (fun k => J (r ≫ ζ ≫ φ k)) :=
      fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
    have e : (Z.presheaf.map (homOfLE le).op).hom ((ζ.app _).hom (b (fun k => J (r ≫ ζ ≫ φ k)))) =
        t.f (fun k => J (r ≫ ζ ≫ φ k)) := fn_ext fun y hy => by
      obtain rfl := hξ y
      refine (gs_res _ y le hy _).trans ((gs_pull _ ζ y _ (le hy) _).trans ?_)
      rw [Category.id_comp]
      exact hb _ (le hy)
    exact ((gs_res r z le hm _).trans (gs_pull r ζ z _ (le hm) _)).symm.trans (congrArg (gs r z _) e)

variable {R : Type} [CommRing R] [IsDomain R]

def genPt (R : Type) [CommRing R] [IsDomain R] : Spec (CommRingCat.of (FractionRing R)) :=
  (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))

theorem eq_genPt (z : Spec (CommRingCat.of (FractionRing R))) : z = genPt R :=
  Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _

theorem exists_psi_of_psiIn {D : DegPre R} {χ : D.X} {I : Ideal R} (h : D.PsiIn χ I) :
    ∃ Ψ : LB.Sec (LB.LinComb D.P.L (Y := Spec (CommRingCat.of R)) (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)),
      ∀ (T : Scheme.{0}) (r : T ⟶ (TK R).left) (z : T) (J), Good D.P.L z J →
        sval Ψ (r ≫ jK R) z J = (val (D.psi χ) r z J).val := by
  obtain ⟨s, hs⟩ := exists_extend D.P.isLB (jK R) (genPt R) eq_genPt (PsiInPull.jK_mem _) (K := PUnit)
    (fun _ => (D.c χ).left) (fun _ => -1) (Geo.Tor.genSec (D.psi χ) (D.psi_gen χ)) (fun q => by
      obtain ⟨p, hp⟩ := exists_chart D.P.isLB ((D.c χ).left q)
      obtain ⟨_, ⟨V, hV, rfl⟩, hvV, hVp⟩ := (Spec (CommRingCat.of R)).isBasis_affineOpens.exists_subset_of_mem_open
        (show q ∈ ((D.c χ).left ⁻¹ᵁ D.P.L.U p : (Spec (CommRingCat.of R)).Opens) from hp)
        ((D.c χ).left ⁻¹ᵁ D.P.L.U p).isOpen
      have h' : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U (fun _ => p) :=
        fun y hy => PsiInPull.mem_wchart _ _ _ _ (hVp hy)
      obtain ⟨a, -, ha⟩ := h (fun _ => p) V hV hVp h'
      have hm : jK R (genPt R) ∈ V := PsiInPull.jK_mem _ V fun h0 => (h0.le hvV : q ∈ (⊥ : (Spec (CommRingCat.of R)).Opens))
      refine ⟨fun _ => p, V, a, hvV, fun y hy => PsiInPull.mem_wchart _ _ _ _ (hVp hy), ?_⟩
      have e := gs_pull (𝟙 _) (jK R) (genPt R) V hm a
      rw [Category.id_comp] at e
      rw [← e, ha]
      exact gs_res (𝟙 _) (genPt R) h' hm _)
  exact ⟨s, fun T r z J hJ => (hs T r z J hJ).trans (sval_genSec (D.psi χ) (D.psi_gen χ) r z hJ)⟩

theorem local_inv {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens} (ψ : PsiOn D W) (ρ : D.X)
    (g : Γ(Spec (CommRingCat.of R), ⊤)) (hgW : (Spec (CommRingCat.of R)).basicOpen g ≤ W)
    (hg : jK R (genPt R) ∈ (Spec (CommRingCat.of R)).basicOpen g) (q : Spec (CommRingCat.of R)) :
    ∃ (j : D.P.L.ι) (V : (Spec (CommRingCat.of R)).Opens) (n : ℕ) (a : Γ(Spec (CommRingCat.of R), V)), q ∈ V ∧
      V ≤ (D.c ρ).left ⁻¹ᵁ D.P.L.U j ∧ gs (jK R) (genPt R) V a = gs (jK R) (genPt R) ⊤ g ^ n *
        ((gm (𝟙 _) (genPt R) (LB.wchart D.P.L (fun _ : PUnit => D.xK ρ) (fun _ => j))
          ((D.psi ρ).s (fun _ => j)))⁻¹).val := by
  obtain ⟨p, hp⟩ := exists_chart D.P.isLB ((D.c ρ).left q)
  obtain ⟨_, ⟨V, hV, rfl⟩, hvV, hVp⟩ := (Spec (CommRingCat.of R)).isBasis_affineOpens.exists_subset_of_mem_open
    (show q ∈ ((D.c ρ).left ⁻¹ᵁ D.P.L.U p : (Spec (CommRingCat.of R)).Opens) from hp)
    ((D.c ρ).left ⁻¹ᵁ D.P.L.U p).isOpen
  have hm : jK R (genPt R) ∈ V := PsiInPull.jK_mem _ V fun h0 => (h0.le hvV : q ∈ (⊥ : (Spec (CommRingCat.of R)).Opens))
  set V' := (Spec (CommRingCat.of R)).basicOpen (resTop V g) with hV'
  have eV : V' = V ⊓ (Spec (CommRingCat.of R)).basicOpen g := Scheme.basicOpen_res _ _ _
  have hW : V' ≤ W := eV.le.trans (inf_le_right.trans hgW)
  have hVV : V' ≤ V := eV.le.trans inf_le_left
  have hm' : jK R (genPt R) ∈ V' := eV.ge ⟨hm, hg⟩
  have hle : W.ι ⁻¹ᵁ V' ≤ LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c ρ).left) (fun _ => p) :=
    fun y hy => PsiInPull.mem_wchart _ _ _ _ (hVp (hVV hy))
  have : IsIso (W.ι.app V') := Scheme.Hom.isIso_app W.ι V' (by rw [Scheme.Opens.opensRange_ι]; exact hW)
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (W.ι.app V')).2
    ((W.toScheme.presheaf.map (homOfLE hle).op).hom (((ψ.psi ρ).s (fun _ => p))⁻¹).val)
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen _ V hV (resTop V g) x
  refine ⟨p, V, n, y, hvV, hVp, ?_⟩
  have hW0 : jK R (genPt R) ∈ W := hW hm'
  let lf : Spec (CommRingCat.of (FractionRing R)) ⟶ (jK R ⁻¹ᵁ W).toScheme :=
    IsOpenImmersion.lift (jK R ⁻¹ᵁ W).ι (𝟙 _) (by
      rintro _ ⟨z, rfl⟩
      obtain rfl := eq_genPt z
      exact ⟨⟨_, hW0⟩, rfl⟩)
  have hlf : lf ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  have hι : (lf ≫ (jK R ∣_ W)) ≫ W.ι = jK R := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hlf, Category.id_comp]
  have hpt : (lf ≫ (jK R ∣_ W)) (genPt R) ∈ W.ι ⁻¹ᵁ V' := (congrArg (fun m => m (genPt R) ∈ V') hι).mpr hm'
  obtain ⟨J, hJ, hJp⟩ := exists_good D.P.L D.P.isLB (genPt R) (fun _ : PUnit => D.xK ρ) (fun _ => p)
    (fun _ _ _ => rfl) (fun _ => hVp hm)
  have e₀ := val_corr hJ (ψ.psi_eq ρ) lf
  rw [val_pull hJ, val_pull hJ, hlf, val_of _ _ _ J (fun _ => p) (fun _ => by
      refine Eq.trans (congrArg J ?_) (hJp PUnit.unit)
      show (lf ≫ (jK R ∣_ W)) ≫ W.ι ≫ (D.c ρ).left = jK R ≫ (D.c ρ).left
      rw [← Category.assoc, hι]),
    val_of _ _ _ J (fun _ => p) (fun _ => by rw [Category.id_comp]; exact hJp PUnit.unit)] at e₀
  have e₁ : gs (jK R) (genPt R) V' x = ((gm (𝟙 _) (genPt R) (LB.wchart D.P.L (fun _ : PUnit => D.xK ρ) (fun _ => p))
      ((D.psi ρ).s (fun _ => p)))⁻¹).val := by
    rw [← e₀]
    refine (congrArg (fun m => gs m (genPt R) V' x) hι).symm.trans ((gs_pull _ W.ι _ V' hpt x).symm.trans ?_)
    refine (congrArg (gs (lf ≫ (jK R ∣_ W)) (genPt R) (W.ι ⁻¹ᵁ V')) hx).trans ?_
    exact (gs_res _ _ hle hpt _).trans ((gs_unit _ _ _ (hle hpt) _).trans (congrArg Units.val (map_inv _ _)))
  have e₂ := congrArg (gs (jK R) (genPt R) V') hy
  refine (gs_res _ _ hVV hm' y).symm.trans (e₂.trans ((gs_mul _ _ _ hm' _ _).trans (congrArg₂ (· * ·) ?_ e₁)))
  rw [gs_eq _ _ _ hm', map_pow, map_pow, ← gs_eq _ _ _ hm']
  exact congrArg (· ^ n) ((gs_res _ _ hVV hm' _).trans (gs_res _ _ le_top hm _))

theorem sval_secScale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top (hJ.mem _ r) _) rfl)

theorem gs_pow {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (c : Γ(Y, ⊤)) (n : ℕ) : gs r z ⊤ (c ^ n) = gs r z ⊤ c ^ n := by
  rw [gs_eq r z ⊤ trivial, gs_eq r z ⊤ trivial, map_pow, map_pow]

theorem exists_inv {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens} (ψ : PsiOn D W) (ρ : D.X)
    (p : Spec (CommRingCat.of R)) (hp : p ∈ W) : ∃ r : R, r ∉ p.asIdeal ∧
      ∃ Φ : LB.Sec (LB.LinComb D.P.L (Y := Spec (CommRingCat.of R)) (K := PUnit) (fun _ => (D.c ρ).left)
        (fun _ => - -1)), ∀ (T : Scheme.{0}) (τ : T ⟶ (TK R).left) (z : T) (J), Good D.P.L z J →
        sval Φ (τ ≫ jK R) z J = gs (τ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) *
          ((val (D.psi ρ) τ z J)⁻¹).val := by
  classical
  obtain ⟨_, ⟨r₀, rfl⟩, hp₀, hW⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (u := W.1) hp W.isOpen
  set g : Γ(Spec (CommRingCat.of R), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r₀ with hg
  have eg : (Spec (CommRingCat.of R)).basicOpen g = PrimeSpectrum.basicOpen r₀ :=
    basicOpen_eq_of_affine (R := CommRingCat.of R) r₀
  have hgen : jK R (genPt R) ∈ (Spec (CommRingCat.of R)).basicOpen g := PsiInPull.jK_mem _ _ fun h0 =>
    (h0.le (eg.ge hp₀) : p ∈ (⊥ : (Spec (CommRingCat.of R)).Opens))
  choose j V n a hq hV ha using local_inv ψ ρ g (eg.le.trans hW) hgen
  obtain ⟨S, hS⟩ := (isCompact_univ (X := Spec (CommRingCat.of R))).elim_finite_subcover (fun q => (V q : Set (Spec (CommRingCat.of R))))
    (fun q => (V q).isOpen) (fun q _ => Set.mem_iUnion.2 ⟨q, hq q⟩)
  have hN : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (r₀ ^ (∑ q ∈ S, n q)) = g ^ (∑ q ∈ S, n q) := map_pow _ _ _
  have hc : ∀ (T : Scheme.{0}) (τ : T ⟶ (TK R).left) (z : T), gs τ z ⊤ (scal (jK R) (r₀ ^ (∑ q ∈ S, n q))) =
      gs (τ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (r₀ ^ (∑ q ∈ S, n q))) := fun T τ z =>
    gs_pull τ (jK R) z ⊤ trivial _
  obtain ⟨s, hs⟩ := exists_extend D.P.isLB (jK R) (genPt R) eq_genPt (PsiInPull.jK_mem _) (K := PUnit)
    (fun _ => (D.c ρ).left) (fun _ => - -1) (SecOps.secScale (scal (jK R) (r₀ ^ (∑ q ∈ S, n q)))
      (Geo.Tor.genSec (LB.invGen D.P.L _ _ (D.psi ρ)) (invGen_isGen _ _ _ _ (D.psi_gen ρ)))) (fun q => by
      obtain ⟨q', hq', hqq⟩ : ∃ q' ∈ S, q ∈ V q' := by simpa using hS (Set.mem_univ q)
      have hm : jK R (genPt R) ∈ V q' := PsiInPull.jK_mem _ _ fun h0 =>
        (h0.le hqq : q ∈ (⊥ : (Spec (CommRingCat.of R)).Opens))
      have hm' : (𝟙 (TK R).left : _ ⟶ _) (genPt R) ∈ LB.wchart D.P.L (fun _ : PUnit => D.xK ρ) (fun _ => j q') :=
        PsiInPull.mem_wchart _ _ _ _ (hV q' hm)
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) hq')
      refine ⟨fun _ => j q', V q', resTop _ (g ^ d) * a q', hqq,
        fun y hy => PsiInPull.mem_wchart _ _ _ _ (hV q' hy), ?_⟩
      refine ((gs_mul _ _ _ hm _ _).trans (congrArg₂ (· * ·) (gs_res _ _ le_top hm _) (ha q'))).trans
        (Eq.trans ?_ ((gs_mul _ _ _ hm' _ _).trans (congrArg₂ (· * ·) ((gs_res _ _ le_top hm' _).trans (hc _ _ _))
          ((gs_unit _ _ _ hm' _).trans (congrArg Units.val (map_inv _ _))))).symm)
      rw [hN, hd, gs_pow, gs_pow, ← _root_.mul_assoc, ← pow_add, add_comm d]
      erw [Category.id_comp]
      rfl)
  refine ⟨r₀ ^ (∑ q ∈ S, n q), fun h => hp₀ (p.isPrime.mem_of_pow_mem _ h), s, fun T τ z J hJ => ?_⟩
  refine (hs T τ z J hJ).trans ((sval_secScale _ _ τ z hJ).trans (congrArg₂ (· * ·) (hc T τ z) ?_))
  exact (sval_genSec _ _ τ z hJ).trans (congrArg Units.val (val_inv _ _))

theorem exists_psi {I : Ideal R} (D : DegData R I) (χ : D.toPre.X) :
    ∃ Ψ : LB.Sec (LB.LinComb D.toPre.P.L (Y := Spec (CommRingCat.of R)) (K := PUnit) (fun _ => (D.toPre.c χ).left)
      (fun _ => -1)), ∀ (T : Over (Spec (CommRingCat.of R))) (σ : T ⟶ TF (R := R) (FractionRing R)) (z : T.left) (J),
        Good D.toPre.P.L z J → sval Ψ ((σ.left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) z J =
          (val (D.toPre.psi χ) (σ.left ≫ jFK (R := R) (FractionRing R)) z J).val := by
  by_cases h : χ = 0
  swap
  · obtain ⟨Ψ, hΨ⟩ := exists_psi_of_psiIn (D.psi_pos χ h)
    exact ⟨Ψ, fun T σ z J hJ => hΨ _ _ z J hJ⟩
  subst h
  have c0 : D.toPre.c 0 = 1 := by
    have m : D.toPre.c (0 + 0) = D.toPre.c 0 * D.toPre.c 0 := D.toPre.c_add 0 0
    rw [add_zero] at m
    exact mul_eq_left.1 m.symm
  have c1 : (D.toPre.c 0).left = eSec D.toPre.P.A := by
    rw [c0, Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  obtain ⟨Ψ, hΨ⟩ := exists_sec D.toPre.P.isLB (Y := Spec (CommRingCat.of R)) (K' := PUnit)
    (φ' := fun _ => (D.toPre.c 0).left) (ε' := fun _ => -1) (fun U _ h => by rw [c1])
    (Geo.Tor.genSec (LB.invGen D.toPre.P.L _ _ D.toPre.rig) (invGen_isGen _ _ _ _ D.toPre.rig_gen))
  refine ⟨Ψ, fun T σ z J hJ => (hΨ _ _ z J hJ).trans ((sval_genSec _ _ _ z hJ).trans (congrArg Units.val
    ((val_inv _ _).trans ?_)))⟩
  have C : IsCub (th D.toPre z J) := isCub_cubV D.toPre.cub hJ
  have t := tau_mul σ hJ D.tau_bimult 0 0 0
  have q := UUA.psi_add σ hJ (0 : D.toPre.X) 0
  have c2 : cP D.toPre T 0 = 1 := by simpa using cPoint_nsmul D.toPre T 0 0
  have hpt : ∀ a b c : D.toPre.X, a = b → val (D.toPre.tau a c) (σ.left ≫ jFK (R := R) (FractionRing R)) z J =
      val (D.toPre.tau b c) (σ.left ≫ jFK (R := R) (FractionRing R)) z J := by rintro a b c rfl; rfl
  have hpp : ∀ a b : D.toPre.X, a = b → val (D.toPre.psi a) (σ.left ≫ jFK (R := R) (FractionRing R)) z J =
      val (D.toPre.psi b) (σ.left ≫ jFK (R := R) (FractionRing R)) z J := by rintro a b rfl; rfl
  rw [hpt _ _ _ (add_zero 0), c2, C.face] at t
  rw [hpp _ _ (add_zero 0), ← mul_left_cancel t, _root_.one_mul, _root_.mul_assoc] at q
  have q' := (mul_eq_left.1 q.symm)
  have e : val D.toPre.rigK (σ.left ≫ jFK (R := R) (FractionRing R)) z J =
    val D.toPre.rig ((σ.left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) z J := val_pull hJ _ _ _
  rw [e] at q'
  exact (eq_inv_of_mul_eq_one_left q').symm

open SectionScalarValuation in

theorem exists_move (D : DegPre R) (k : ℕ) (α mu : D.X) {Ix : Type} [Fintype Ix]
    {φV : Ix → (Spec (CommRingCat.of R) ⟶ D.P.A.left)} {εV : Ix → ℤ} (w : LB.Sec (LB.LinComb D.P.L φV εV))
    (hC : ∀ (U : Type) [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U), ∏ i, h (D.P.A.hom ≫ φV i) ^ εV i =
      (h (cQ D D.P.A α * cQ D D.P.A mu).left)⁻¹ * h (cQ D D.P.A α).left * h (cQ D D.P.A mu).left *
        (h (1 : D.P.A ⟶ D.P.A).left)⁻¹ * (h (cQ D D.P.A mu).left ^ k)⁻¹ * h (1 : D.P.A ⟶ D.P.A).left ^ k)
    (s : D.SecB k α) : ∃ f : D.SecB k (α + k • mu),
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
        sval f ρ.left z J = sval s (ρ * cQ D T mu).left z J * (cubN (cubV D.cub z J) k (cQ D T α) (cQ D T mu) ρ *
          (cubV D.cub z J (cQ D T α) ρ (cQ D T mu))⁻¹).val * sval w (ρ.left ≫ D.P.A.hom) z J := by
  set a : D.P.A ⟶ D.P.A := cQ D _ α with ha
  set m : D.P.A ⟶ D.P.A := cQ D _ mu with hm
  have hα' : cQ D D.P.A (α + k • mu) = a * m ^ k := by rw [cQ_add, cQ_nsmul]
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub a m (𝟙 D.P.A) k
  have hu := mulGen_isGen _ _ _ _ _ _ _ hN
    (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen (lift a (lift (𝟙 D.P.A) m)).left))
  obtain ⟨f, vf⟩ := exists_sec D.P.isLB (φ' := D.famφB (α + k • mu)) (ε' := DegPre.famε k) (fun U _ h => by
      have p₁ := prod_cub a (𝟙 D.P.A) m h
      have p₂ := hC U h
      have p₃ := prod_famB D (𝟙 _) (α + k • mu) k h
      have p₄ := prod_famB D (𝟙 D.P.A * m) α k h
      have e₃ : ∀ i, Over.Hom.left (𝟙 D.P.A) ≫ D.famφB (α + k • mu) i = D.famφB (α + k • mu) i := fun i => by simp
      simp only [e₃] at p₃
      rw [hα'] at p₃
      rw [← ha] at p₄
      have q₁ : 𝟙 D.P.A * (a * m ^ k) = a * m ^ k * 𝟙 D.P.A := mul_comm _ _
      have q₂ : 𝟙 D.P.A * m * a = a * 𝟙 D.P.A * m := by rw [mul_comm _ a, ← _root_.mul_assoc]
      have q₃ : m * 𝟙 D.P.A = 𝟙 D.P.A * m := mul_comm _ _
      rw [q₁] at p₃
      rw [q₂] at p₄
      have p₀ : ∏ i : Fin 8, h ((![(a * m ^ k * 𝟙 D.P.A).left, (a * m ^ k).left, (a * 𝟙 D.P.A).left, a.left,
          (m * 𝟙 D.P.A).left, m.left, Over.Hom.left (𝟙 D.P.A), (1 : D.P.A ⟶ D.P.A).left] : Fin 8 → _) i) ^
            (![1, -1, -1, 1, -k, k, k, -k] : Fin 8 → ℤ) i =
          h (a * m ^ k * 𝟙 D.P.A).left * (h (a * m ^ k).left)⁻¹ * (h (a * 𝟙 D.P.A).left)⁻¹ * h a.left *
            (h (𝟙 D.P.A * m).left ^ k)⁻¹ * h m.left ^ k * h (Over.Hom.left (𝟙 D.P.A)) ^ k *
            (h (1 : D.P.A ⟶ D.P.A).left ^ k)⁻¹ := by
        simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, q₃,
          zpow_neg, zpow_one, zpow_natCast, _root_.mul_one, _root_.mul_assoc]
      refine Eq.trans (prod_sum₂ (K := Fin 4 ⊕ (Fin 8 ⊕ thK)) (K' := Ix) (U := U) _
        (prod_sum₂ (K := Fin 4) (K' := Fin 8 ⊕ thK) (U := U) _ p₄
          (prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ p₀ (prod_neg _ _ p₁))) p₂) (Eq.trans ?_ p₃.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (SectionArithmetic.mulSec (pullMulSec s (𝟙 D.P.A * m).left _ hu) (SectionArithmetic.pullSec w D.P.A.hom))
  refine ⟨f, fun T ρ z J hJ => ?_⟩
  refine (vf _ _ z J hJ).trans ((SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    ((sval_pullMulSec _ _ _ hu _ z hJ).trans (congrArg₂ (· * ·) ?_ (congrArg Units.val ?_)))
    (SectionArithmetic.sval_pullSec _ _ _ z hJ)))
  · rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, hm, comp_cQ]
  · refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vN T ρ z J hJ)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.cub ρ hJ _ _ _))))).trans ?_
    rw [ha, hm, comp_cQ, comp_cQ, Category.comp_id]

open SectionScalarValuation in

theorem exists_const {I : Ideal R} (D : DegData R I) (k : ℕ) (ρ mu : D.toPre.X) (r : R)
    (Φ : LB.Sec (LB.LinComb D.toPre.P.L (Y := Spec (CommRingCat.of R)) (K := PUnit) (fun _ => (D.toPre.c ρ).left)
      (fun _ => - -1)))
    (hΦ : ∀ (T : Scheme.{0}) (τ : T ⟶ (TK R).left) (z : T) (J), Good D.toPre.P.L z J →
      sval Φ (τ ≫ jK R) z J = gs (τ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) *
        ((val (D.toPre.psi ρ) τ z J)⁻¹).val) :
    ∃ (Ix : Type) (_ : Fintype Ix) (φV : Ix → (Spec (CommRingCat.of R) ⟶ D.toPre.P.A.left)) (εV : Ix → ℤ)
      (w : LB.Sec (LB.LinComb D.toPre.P.L φV εV)),
      (∀ (U : Type) [CommGroup U] (h : (D.toPre.P.A.left ⟶ D.toPre.P.A.left) → U),
        ∏ i, h (D.toPre.P.A.hom ≫ φV i) ^ εV i =
          (h (cQ D.toPre D.toPre.P.A ρ * cQ D.toPre D.toPre.P.A mu).left)⁻¹ * h (cQ D.toPre D.toPre.P.A ρ).left *
            h (cQ D.toPre D.toPre.P.A mu).left * (h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left)⁻¹ *
            (h (cQ D.toPre D.toPre.P.A mu).left ^ (k + 1))⁻¹ * h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left ^ (k + 1)) ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (σ : T ⟶ TF (R := R) (FractionRing R)) (z : T.left) (J),
        Good D.toPre.P.L z J → sval w ((σ.left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) z J =
          gs ((σ.left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) *
            (val (DegPre.famMult D.toPre (FractionRing R) (k + 1) mu ρ) σ.left z J).val := by
  choose Ψ hΨ using exists_psi D
  refine ⟨_, inferInstance, _, _, SectionArithmetic.mulSec (SectionArithmetic.mulSec (Ψ (mu + ρ)) Φ) (SectionArithmetic.mulSec (SectionArithmetic.powSec fun _ : Fin k => Ψ mu)
    (SectionArithmetic.powSec (L := D.toPre.P.L) (Y := Spec (CommRingCat.of R)) (K := PUnit) (φ := fun _ => eSec D.toPre.P.A)
      (ε := fun _ => 1) fun _ : Fin k => Geo.Tor.genSec D.toPre.rig D.toPre.rig_gen)), fun U _ h => ?_,
    fun T σ z J hJ => ?_⟩
  · have hc : ∀ χ, D.toPre.P.A.hom ≫ (D.toPre.c χ).left = (cQ D.toPre D.toPre.P.A χ).left := fun χ => by simp [cQ]
    have he : D.toPre.P.A.hom ≫ eSec D.toPre.P.A = (1 : D.toPre.P.A ⟶ D.toPre.P.A).left := by
      rw [Hom.one_def]; simp [eSec]
    simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, hc, he,
      cQ_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_punit, Fintype.card_prod,
      _root_.mul_one]
    rw [mul_comm (cQ D.toPre D.toPre.P.A mu)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    module
  · have e : val D.toPre.rigK (σ.left ≫ jFK (R := R) (FractionRing R)) z J =
      val D.toPre.rig ((σ.left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) z J := val_pull hJ _ _ _
    refine ((SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
      ((SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·) (hΨ _ T σ z J hJ) (hΦ _ _ z J hJ)))
      ((SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
        ((SectionArithmetic.sval_powSec _ _ z hJ).trans (Finset.prod_congr rfl fun _ _ => hΨ _ T σ z J hJ))
        ((SectionArithmetic.sval_powSec _ _ z hJ).trans (Finset.prod_congr rfl fun _ _ =>
          (sval_genSec _ _ _ z hJ).trans (congrArg Units.val e.symm))))))).trans ?_
    rw [val_famMult σ hJ, UUA.val_powGen', UUA.val_powGen', UUA.psi_add σ hJ, Finset.prod_const, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    linear_combination (gs ((σ.left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) *
      (val (D.toPre.tau mu ρ) (σ.left ≫ jFK (R := R) (FractionRing R)) z J).val *
      (val (D.toPre.psi mu) (σ.left ≫ jFK (R := R) (FractionRing R)) z J).val ^ (k + 1) *
      (val D.toPre.rigK (σ.left ≫ jFK (R := R) (FractionRing R)) z J).val ^ (k + 1)) *
      (val (D.toPre.psi ρ) (σ.left ≫ jFK (R := R) (FractionRing R)) z J).mul_inv

end FamIntAt

open FamIntAt SectionScalarValuation in

theorem integralFamily_at_prime : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (W : (Spec (CommRingCat.of R)).Opens), Nonempty (PsiOn D.toPre W) → ∀ p : (Spec (CommRingCat.of R)), p ∈ W → ∀ (k : ℕ), 1 ≤ k → ∀ (ρ : D.toPre.X) (s : D.toPre.SecB k ρ), ∃ r : R, r ∉ p.asIdeal ∧ ∃ (F : Fam D.toPre (FractionRing R) k) (f : ∀ α, D.toPre.SecB k α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α) (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧ (∀ j, (f ρ).f j = resTop _ (scal D.toPre.P.A.hom r) * (s).f j) ∧ ∀ β, (∀ mu, ρ + k • mu ≠ β) → ∀ j, (f β).f j = 0 := by
  intro hG R _ _ I _ D W ⟨ψ⟩ p hp k hk ρ s
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨r, hr, Φ₀, hΦ₀⟩ := exists_inv ψ ρ p hp
  let β : D.toPre.SecB (k + 1) ρ := SecOps.secScale (scal D.toPre.P.A.hom r) s
  obtain ⟨σ, hσ⟩ := exists_sec hL (φ' := DegPre.famφ D.toPre (FractionRing R) ρ) (ε' := DegPre.famε (k + 1))
    (fun U _ g => Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq])
    (SectionArithmetic.pullSec β (DegPre.prB D.toPre (FractionRing R)).left)
  obtain ⟨Φ, hΦ, hΦ0⟩ := UUA.exists_fam_rep (F := FractionRing R) hG D.tau_bimult (k + 1) ρ (fun a b h => by
    have h' : ((k + 1 : ℕ) : ℤ) • a = ((k + 1 : ℕ) : ℤ) • b := by
      rw [natCast_zsmul, natCast_zsmul]; exact add_left_cancel h
    exact smul_right_injective D.toPre.X (by omega : ((k + 1 : ℕ) : ℤ) ≠ 0) h') σ
  have key : ∀ α : D.toPre.X, ∃ f : D.toPre.SecB (k + 1) α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε (k + 1)) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε (k + 1)) f (DegPre.prB D.toPre (FractionRing R)).left 1 ∧
      (∀ h : ρ = α, f = h ▸ β) ∧ ((∀ mu, ρ + (k + 1) • mu ≠ α) → ∀ j, f.f j = 0) := by
    intro α
    by_cases hα : ρ = α
    · subst hα
      refine ⟨β, secScal_of_sval hL fun y J hJ => ?_, fun _ => rfl, fun h => absurd (by simp) (h 0)⟩
      rw [hΦ]
      exact ((hσ _ _ y J hJ).trans (SectionArithmetic.sval_pullSec _ _ _ y hJ)).symm
    by_cases hc : ∃ mu, ρ + (k + 1) • mu = α
    · obtain ⟨mu, rfl⟩ := hc
      obtain ⟨Ix, _, φV, εV, w, hC, hw⟩ := exists_const D k ρ mu r Φ₀ hΦ₀
      obtain ⟨f, hf⟩ := exists_move D.toPre (k + 1) ρ mu w hC s
      refine ⟨f, secScal_of_sval hL fun y J hJ => ?_, fun h => absurd h hα, fun h => absurd rfl (h mu)⟩
      obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D.toPre) (F := FractionRing R) hG (k + 1) mu ρ
      have e₁ := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (Φ.fe mu ρ u hu hc) _ (𝟙 _) y J hJ
      have e₂ := hv u hu hc _ (𝟙 _) y J hJ
      rw [uVal_id, Over.id_left, Category.id_comp, comp_cP] at e₂
      have e₃ := hf _ (DegPre.prB D.toPre (FractionRing R)) y J hJ
      have e₄ := hw _ (fst (TF (R := R) (FractionRing R)) D.toPre.P.A) y J hJ
      have a₁ : (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom =
          ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
        rw [Over.w, Category.assoc]
        exact (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).symm
      have a₂ : (DegPre.trF D.toPre (FractionRing R) mu).left ≫ (DegPre.prB D.toPre (FractionRing R)).left =
          (DegPre.prB D.toPre (FractionRing R) * cQ D.toPre _ mu).left := by
        rw [← Over.comp_left, DegPre.trF, DegPre.prB, lift_snd]
        rfl
      have a₃ : (DegPre.prB D.toPre (FractionRing R) * cQ D.toPre _ mu).left ≫ D.toPre.P.A.hom =
          ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R :=
        (Over.w _).trans ((Over.w _).symm.trans a₁)
      have e₅ : sval σ (DegPre.trF D.toPre (FractionRing R) mu).left y J =
          gs (((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) y ⊤
            ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) *
          sval s (DegPre.prB D.toPre (FractionRing R) * cQ D.toPre _ mu).left y J := by
        refine (hσ _ _ y J hJ).trans ((SectionArithmetic.sval_pullSec _ _ _ y hJ).trans ?_)
        rw [a₂, ← a₃]
        exact (sval_secScale _ _ _ y hJ).trans (congrArg₂ (· * ·) (gs_pull _ D.toPre.P.A.hom y ⊤ trivial _) rfl)
      rw [a₁, e₄] at e₃
      rw [Category.id_comp, hΦ, e₅, e₂, Units.val_mul] at e₁
      rw [Category.id_comp, e₃, e₁]
      exact (mul_left_comm _ _ _).trans (by rw [_root_.mul_assoc, _root_.mul_assoc]; rfl)
    · refine ⟨SecOps.secZero, secScal_of_sval hL fun y J hJ => ?_, fun h => absurd h hα, fun _ _ => rfl⟩
      rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
        UUA.sval_zero_of (hΦ0 α fun mu e => hc ⟨mu, e⟩) _ y J (hJ.mem _ _)]
  choose f h1 h2 h3 using key
  exact ⟨r, hr, Φ, f, h1, fun j => congrArg (fun t => t.f j) (h2 ρ rfl), h3⟩

end GlobalTheory
