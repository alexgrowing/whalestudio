import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecOfCompatible
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquivStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomExtOfSecPullEq
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Algebraise

open ReciprocityTheory.ChartRestriction.G.Geo.Tor SectionRingIso TopologicalSpace

section General

variable {X X' Y Y₂ Z : Scheme.{0}} {L : LB X} {L' : LB X'}

theorem gm_pull_g (g : Y ⟶ X) (r : Z ⟶ Y) (z : Z) {j j' : L.ι} (hj : g (r z) ∈ L.U j) (hj' : g (r z) ∈ L.U j') :
    gm r z ((L.pull g).U (fun _ => j) ⊓ (L.pull g).U (fun _ => j')) ((L.pull g).g (fun _ => j) (fun _ => j')) =
      gm (r ≫ g) z _ (L.g j j') := by
  have hp : r z ∈ (L.pull g).U (fun _ => j) ⊓ (L.pull g).U (fun _ => j') := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm r z _ (∏ _k : PUnit, (res _ (pullU g _ (L.g j j'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res r z _ hp _).trans (gm_pull r g z (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _)

theorem mem_wc {g : Y ⟶ X} {j : Fin 1 → L.ι} {y : Y} :
    y ∈ LB.wchart L (fun _ : Fin 1 => g) j ↔ g y ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact h⟩

theorem fin_one_const {α : Type} (p : Fin 1 → α) : p = fun _ => p 0 :=
  funext fun κ => congrArg p (Subsingleton.elim _ _)

theorem exists_conv (g : Y ⟶ X) {n : ℕ} (s : H0 (L.pull g) n) :
    ∃ s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => (n : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j →
        gs r z (LB.wchart L (fun _ : Fin 1 => g) (fun _ => j)) (s'.f fun _ => j) = vl s r z (fun _ _ => j) := by
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => g) j ≤ ch (L.pull g) (fun _ _ => j 0) :=
    fun j y hy => mem_ch.2 (mem_pull.2 (mem_wc.1 hy))
  refine ⟨LBGerm.secOfGerm (M := LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => (n : ℤ)))
    (fun j => (Y.presheaf.map (homOfLE (le j)).op).hom (s.f fun _ _ => j 0)) fun y j j' hj hj' => ?_,
    fun Z r z j hj => gs_res r z (le _) (mem_wc.2 hj) _⟩
  refine (gs_res (𝟙 Y) y (le j) hj _).trans ((vl_trans s (𝟙 Y) y (j := fun _ _ => j 0) (j' := fun _ _ => j' 0)
    (mem_pull.2 (mem_wc.1 hj)) (mem_pull.2 (mem_wc.1 hj'))).trans
    (congrArg₂ (· * ·) ?_ (gs_res (𝟙 Y) y (le j') hj' _).symm))
  refine Eq.trans ?_ (congrArg Units.val
    (gm_linComb L (fun _ : Fin 1 => g) (fun _ => (n : ℤ)) (𝟙 Y) y j j' hj hj')).symm
  rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
  exact congrArg (fun u : (Y.presheaf.stalk y)ˣ => u.val ^ n) (gm_pull_g g (𝟙 Y) y (mem_wc.1 hj) (mem_wc.1 hj'))

theorem exists_down (hL : L.IsLB) (hL' : L'.IsLB) (g : Y ⟶ X) (g' : Y ⟶ X') (v : LB.Iso (L'.pull g') (L.pull g))
    (hv : v.IsGen) {n : ℕ} (b : H0 L n) :
    ∃ s : LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => g') (fun _ => (n : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι) (j' : L'.ι), g (r z) ∈ L.U j → g' (r z) ∈ L'.U j' →
        vl b (r ≫ g) z (fun _ => j) = (gw v r z j (fun _ => j')).val ^ n *
          gs r z (LB.wchart L' (fun _ : Fin 1 => g') (fun _ => j')) (s.f fun _ => j') := by
  obtain ⟨a, ha, -⟩ := SecPull.existsUnique_secPull X Y X Y L (L'.pull g') g hL (LB.isLB_pull hL' g') v hv (Fin 1)
    (fun _ => 𝟙 Y) (fun _ => 𝟙 X) (fun _ => (n : ℤ)) g (fun _ => by simp) b
  obtain ⟨s, hs⟩ := exists_conv g' a
  refine ⟨s, fun Z r z j j' hj hj' => ?_⟩
  rw [hs Z r z j' hj']
  refine (ha Z r z (fun _ => j) (fun _ _ => j') (fun _ => hj) (fun _ => mem_pull.2 hj')).trans ?_
  rw [Fin.prod_univ_one, Category.comp_id, zpow_natCast, Units.val_pow_eq_pow_val]

theorem exists_swap (g : Y ⟶ X) (g' : Y ⟶ X') (v : LB.Iso (L'.pull g') (L.pull g)) (hv : v.IsGen) (ψ : Y₂ ⟶ Y)
    (g₂ : Y₂ ⟶ X) (g₂' : Y₂ ⟶ X') (e : ψ ≫ g = g₂) (e' : ψ ≫ g' = g₂') :
    ∃ u : LB.Iso (L.pull g₂) (L'.pull g₂'), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₂) (z : Z) (j : L.ι) (j' : L'.ι), g₂ (r z) ∈ L.U j → g₂' (r z) ∈ L'.U j' →
        gw u r z j' (fun _ => j) = (gw v (r ≫ ψ) z j (fun _ => j'))⁻¹ := by
  subst e e'
  have le : ∀ (J : PUnit → L.ι) (J' : PUnit → L'.ι), (L'.pull (ψ ≫ g')).U J' ⊓ (L.pull (ψ ≫ g)).U J ≤
      ψ ⁻¹ᵁ ((L.pull g).U J ⊓ (L'.pull g').U J') := fun J J' y hy =>
    ⟨mem_pull.2 (mem_pull₂.1 hy.2), mem_pull.2 (mem_pull₂.1 hy.1)⟩
  let u : LB.Iso (L.pull (ψ ≫ g)) (L'.pull (ψ ≫ g')) :=
    ⟨fun p => (res (le p.2 p.1) (pullU ψ _ (v.s (p.2, p.1))))⁻¹⟩
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₂) (z : Z) (j : L.ι) (j' : L'.ι), (ψ ≫ g) (r z) ∈ L.U j →
      (ψ ≫ g') (r z) ∈ L'.U j' → gw u r z j' (fun _ => j) = (gw v (r ≫ ψ) z j (fun _ => j'))⁻¹ := by
    intro Z r z j j' hj hj'
    have hm : r z ∈ (L'.pull (ψ ≫ g')).U (fun _ => j') ⊓ (L.pull (ψ ≫ g)).U (fun _ => j) :=
      ⟨mem_pull.2 hj', mem_pull.2 hj⟩
    exact (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res r z (le _ _) hm _).trans (gm_pull r ψ z _ (le _ _ hm) _)))
  refine ⟨u, (isGen_iff u).2 fun Z r z j j' k k' hj hj' hk hk' => ?_, hu⟩
  have hk₀ := mem_pull.1 hk
  have hk₀' := mem_pull.1 hk'
  have h₁ := hu Z r z (k PUnit.unit) j hk₀ hj
  have h₂ := hu Z r z (k' PUnit.unit) j' hk₀' hj'
  have h₃ := (isGen_iff v).1 hv Z (r ≫ ψ) z (k PUnit.unit) (k' PUnit.unit) (fun _ => j) (fun _ => j') hk₀ hk₀'
    (mem_pull.2 hj) (mem_pull.2 hj')
  have h₄ := gm_pull_g (ψ ≫ g) r z hk₀ hk₀'
  rw [gm_pull_g g' (r ≫ ψ) z hj hj', Category.assoc, Category.assoc] at h₃
  refine h₁.trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg (fun t => _ * t⁻¹) h₄) h₂).symm)
  rw [h₃, mul_inv, mul_inv, inv_inv, mul_comm (_⁻¹) (gm (r ≫ ψ ≫ g') z _ _)]

theorem vl_add_scale {n : ℕ} {a b d : H0 L n} {c : Γ(X, ⊤)} (h : ∀ j, d.f j = a.f j + resTop _ c * b.f j)
    (r : Z ⟶ X) (z : Z) {j : L.ι} (hj : r z ∈ L.U j) :
    vl d r z (fun _ => j) = vl a r z (fun _ => j) + gs r z ⊤ c * vl b r z (fun _ => j) := by
  have hm : r z ∈ ch L (fun _ => j) := mem_ch.2 hj
  exact (congrArg (gs r z (ch L fun _ => j)) (h _)).trans ((gs_add r z _ hm _ _).trans (congrArg (_ + ·)
    ((gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z _ hm _)))))

theorem vl_mul {n m : ℕ} {a : H0 L n} {b : H0 L m} {d : H0 L (n + m)} (h : ∀ j : Fin 1 → L.ι,
    (show Γ(X, ch L j) from d.f j) = (show Γ(X, ch L j) from a.f j) * (show Γ(X, ch L j) from b.f j))
    (r : Z ⟶ X) (z : Z) {j : L.ι} (hj : r z ∈ L.U j) :
    vl d r z (fun _ => j) = vl a r z (fun _ => j) * vl b r z (fun _ => j) :=
  (congrArg (gs r z (ch L fun _ => j)) (h _)).trans (gs_mul r z _ (mem_ch.2 hj) _ _)

theorem locus_mul (hL : L.IsLB) {n m : ℕ} {a : H0 L n} {b : H0 L m} {d : H0 L (n + m)} (h : ∀ j : Fin 1 → L.ι,
    (show Γ(X, ch L j) from d.f j) = (show Γ(X, ch L j) from a.f j) * (show Γ(X, ch L j) from b.f j)) :
    nonzeroLocus d = nonzeroLocus a ⊓ nonzeroLocus b := by
  ext x
  obtain ⟨j, hj⟩ := exists_chart hL x
  refine (mem_iff_isUnit d (𝟙 X) x (j := fun _ => j) hj).trans ?_
  rw [vl_mul h (𝟙 X) x hj, IsUnit.mul_iff]
  exact (and_congr (mem_iff_isUnit a (𝟙 X) x (j := fun _ => j) hj)
    (mem_iff_isUnit b (𝟙 X) x (j := fun _ => j) hj)).symm

theorem gs_scal {R : Type} [CommRing R] (p : X ⟶ Spec (CommRingCat.of R)) (c : R) (r : Z ⟶ X) (z : Z) :
    gs r z ⊤ (scal p c) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) :=
  gs_pull r p z ⊤ trivial _

def Rel {T : ℕ → Scheme.{0}} (g : ∀ e, T e ⟶ X) (g' : ∀ e, T e ⟶ X')
    (v : ∀ e, LB.Iso (L'.pull (g' e)) (L.pull (g e))) {n : ℕ} (a : H0 L' n) (b : H0 L n) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T e) (z : Z) (j : L.ι) (j' : L'.ι), g e (r z) ∈ L.U j → g' e (r z) ∈ L'.U j' →
    vl b (r ≫ g e) z (fun _ => j) = (gw (v e) r z j (fun _ => j')).val ^ n * vl a (r ≫ g' e) z (fun _ => j')

theorem Rel.mem_iff (hL : L.IsLB) (hL' : L'.IsLB) {T : ℕ → Scheme.{0}} {g : ∀ e, T e ⟶ X} {g' : ∀ e, T e ⟶ X'}
    {v : ∀ e, LB.Iso (L'.pull (g' e)) (L.pull (g e))} {n : ℕ} {a : H0 L' n} {b : H0 L n} (h : Rel g g' v a b)
    (e : ℕ) (z : T e) : g e z ∈ nonzeroLocus b ↔ g' e z ∈ nonzeroLocus a := by
  obtain ⟨j, hj⟩ := exists_chart hL (g e z)
  obtain ⟨j', hj'⟩ := exists_chart hL' (g' e z)
  have := h e _ (𝟙 _) z j j' hj hj'
  rw [Category.id_comp, Category.id_comp] at this
  rw [mem_iff_isUnit b _ z (j := fun _ => j) hj, mem_iff_isUnit a _ z (j := fun _ => j') hj', this,
    ← Units.val_pow_eq_pow_val, Units.isUnit_units_mul]

end General

section Thick

variable {R : Type} [CommRing R] [IsLocalRing R] (I : Ideal R) [IsAdicComplete I R]

omit [IsLocalRing R] [IsAdicComplete I R] in
theorem thickMap_fstG (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

omit [IsLocalRing R] [IsAdicComplete I R] in
theorem fstG_hom (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    (fstG I e G).left ≫ G.hom = (thickObj R I e G).hom ≫ thick R I e :=
  pullback.condition

theorem eq_top_of_thick (G : Over (Spec (CommRingCat.of R))) [UniversallyClosed G.hom] (W : G.left.Opens)
    (h : ∀ z, (fstG I 0 G).left z ∈ W) : W = ⊤ := by
  by_contra hW
  obtain ⟨x, hx⟩ : ∃ x, x ∉ W := by
    by_contra! H
    exact hW (top_le_iff.1 fun x _ => H x)
  have hc : IsClosed (G.hom '' (W : Set G.left)ᶜ) := G.hom.isClosedMap _ W.isOpen.isClosed_compl
  obtain ⟨y, hy, e⟩ : IsLocalRing.closedPoint R ∈ G.hom '' (W : Set G.left)ᶜ :=
    (IsLocalRing.specializes_closedPoint (G.hom x)).mem_closed hc ⟨x, hx, rfl⟩
  have hm : G.hom y ∈ Set.range (thick R I 0) := by
    rw [e]
    have : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (0 + 1)))) = _ :=
      range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective
    refine this.ge ?_
    rw [PrimeSpectrum.mem_zeroLocus, Ideal.mk_ker, zero_add, pow_one]
    exact (IsAdicComplete.le_jacobson_bot I).trans (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).le
  obtain ⟨z, hz⟩ : y ∈ Set.range (pullback.fst G.hom (thick R I 0)) := by
    rw [Scheme.Pullback.range_fst]; exact hm
  exact hy (hz ▸ h z)

variable [IsNoetherianRing R]

omit [IsLocalRing R] in

theorem exists_cover (hA : AmpleSt) (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ) (hn : 4 ≤ n) :
    ∃ (κ : Type) (s : κ → H0 P.L n), (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
  obtain ⟨m, s, hcov, hs⟩ := (hA _ P n hn).2 ⊤ (isAffineOpen_top _)
  have : IsIso (P.A.hom ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso (P.A.left.topIso).hom)
  let ψ := inv (P.A.hom ⁻¹ᵁ ⊤).ι
  have hψ : ψ ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ := IsIso.inv_hom_id _
  have loc := fun i => VeryAmpleCharts.locus_move P.L n hψ P.isLB (s i)
  choose t ht _ using fun i => exists_sec_oneTerm P.L (K' := Fin 1) rfl (VeryAmpleCharts.move P.L n hψ (s i))
  refine ⟨_, t, ?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact Opens.mem_iSup.2 ⟨i, ((ht i).trans (loc i)).ge hi⟩
  · exact ((ht i).trans (loc i)) ▸ (hs i).1.preimage ψ

theorem existsUnique_rel (hS : SecBaseChangeSt) (P : PolAV (Spec (CommRingCat.of R))) {X : Scheme.{0}} {L : LB X}
    (hL : L.IsLB) (g : ∀ e, (thickObj R I e P.A).left ⟶ X)
    (v : ∀ e, LB.Iso (P.L.pull (fstG I e P.A).left) (L.pull (g e))) (hv : ∀ e, (v e).IsGen)
    (hg : ∀ e, thickMap R I e P.A ≫ g (e + 1) = g e)
    (hc : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (j : L.ι) (j' : P.L.ι),
      g e (r z) ∈ L.U j → (fstG I e P.A).left (r z) ∈ P.L.U j' →
      gw (v (e + 1)) (r ≫ thickMap R I e P.A) z j (fun _ => j') = gw (v e) r z j (fun _ => j'))
    {n : ℕ} (hn : 1 ≤ n) (b : H0 L n) :
    ∃! a : H0 P.L n, Rel (T := fun e => (thickObj R I e P.A).left) g (fun e => (fstG I e P.A).left) v a b := by
  choose s hs using fun e => exists_down hL P.isLB (g e) (fstG I e P.A).left (v e) (hv e) b
  have cancel : ∀ {T : Type} [CommRing T] (u : Tˣ) {x y : T}, u.val ^ n * x = u.val ^ n * y → x = y :=
    fun u _ _ h => (u.isUnit.pow n).mul_left_cancel h
  have sv : ∀ (a : H0 P.L n) (Z : Scheme.{0}) (q : Z ⟶ P.A.left) (z : Z) (J),
      sval a q z J = vl a q z (fun _ => J q) := fun a Z q z J =>
    sval_of a q z J (fun _ => J q) fun _ => by rw [Category.comp_id]
  obtain ⟨a, ha, hu⟩ := SectionLimit.existsUnique_sec_of_compatible hS R I P n hn s fun e Z r z J hJ => by
    obtain ⟨j, hj⟩ := exists_chart hL (g e (r z))
    have hj' : (fstG I e P.A).left (r z) ∈ P.L.U (J (r ≫ (fstG I e P.A).left)) := hJ _
    have e₁ : (r ≫ thickMap R I e P.A) ≫ g (e + 1) = r ≫ g e := by rw [Category.assoc, hg]
    have e₂ : (r ≫ thickMap R I e P.A) ≫ (fstG I (e + 1) P.A).left = r ≫ (fstG I e P.A).left := by
      rw [Category.assoc, thickMap_fstG]
    have h₁ := hs (e + 1) Z (r ≫ thickMap R I e P.A) z j (J (r ≫ (fstG I e P.A).left))
      ((congrArg (fun q : Z ⟶ X => q z ∈ L.U j) e₁).mpr hj)
      ((congrArg (fun q : Z ⟶ P.A.left => q z ∈ P.L.U _) e₂).mpr hj')
    rw [e₁, hc e Z r z j _ hj hj', hs e Z r z j _ hj hj'] at h₁
    exact (sval_of (s (e + 1)) _ z J (fun _ => J (r ≫ (fstG I e P.A).left)) fun _ => congrArg J e₂).trans
      (cancel _ h₁).symm
  refine ⟨a, fun e Z r z j j' hj hj' => ?_, fun a' ha' => hu a' fun e Z r z J hJ => ?_⟩
  · obtain ⟨J, hJ, eJ⟩ := exists_good P.L P.isLB z (K := Fin 1) (fun _ => r ≫ (fstG I e P.A).left) (fun _ => j')
      (fun _ _ _ => rfl) (fun _ => hj')
    have := ha e Z r z J hJ
    rw [sv, eJ 0, sval_of (s e) r z J (fun _ => j') fun _ => eJ 0] at this
    rw [this]
    exact hs e Z r z j j' hj hj'
  · obtain ⟨j, hj⟩ := exists_chart hL (g e (r z))
    have hj' : (fstG I e P.A).left (r z) ∈ P.L.U (J (r ≫ (fstG I e P.A).left)) := hJ _
    rw [sv]
    exact cancel _ ((ha' e Z r z j _ hj hj').symm.trans (hs e Z r z j _ hj hj'))

end Thick

end GlobalTheory.Algebraise

open GlobalTheory.Algebraise GlobalTheory.SectionRingIso ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace in

theorem GlobalTheory.exists_iso_of_compatible_thickenings : SecBaseChangeSt → AmpleSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P P' : PolAV (Spec (CommRingCat.of R))) (β : ∀ e : ℕ, thickObj R I e P'.A ≅ thickObj R I e P.A) (v : ∀ e : ℕ, LB.Iso (P'.L.pull (fstG I e P'.A).left) (P.L.pull ((β e).hom.left ≫ (fstG I e P.A).left))), (∀ e, (v e).IsGen) → (∀ e, thickMap R I e P'.A ≫ (β (e + 1)).hom.left = (β e).hom.left ≫ thickMap R I e P.A) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : P.L.ι) (j' : P'.L.ι), (fstG I e P.A).left ((β e).hom.left (r z)) ∈ P.L.U j → (fstG I e P'.A).left (r z) ∈ P'.L.U j' → Geo.Tor.gw (v (e + 1)) (r ≫ thickMap R I e P'.A) z j (fun _ => j') = Geo.Tor.gw (v e) r z j (fun _ => j')) → ∃ (Φ : P'.A ≅ P.A) (w : LB.Iso P'.L (P.L.pull Φ.hom.left)), w.IsGen ∧ ∀ e : ℕ, (fstG I e P'.A).left ≫ Φ.hom.left = (β e).hom.left ≫ (fstG I e P.A).left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : P.L.ι) (j' : P'.L.ι), (fstG I e P.A).left ((β e).hom.left (r z)) ∈ P.L.U j → (fstG I e P'.A).left (r z) ∈ P'.L.U j' → Geo.Tor.gw w (r ≫ (fstG I e P'.A).left) z j j' = Geo.Tor.gw (v e) r z j (fun _ => j') := by
  intro hS hA R _ _ _ I _ P P' β v hv hβ hc
  have prop : ∀ Q : PolAV (Spec (CommRingCat.of R)), IsProper Q.A.hom := fun Q => Q.isAb.proper
  have cpt : ∀ Q : PolAV (Spec (CommRingCat.of R)), CompactSpace Q.A.left := fun Q =>
    have := prop Q; QuasiCompact.compactSpace_of_compactSpace Q.A.hom
  have qs : ∀ Q : PolAV (Spec (CommRingCat.of R)), QuasiSeparatedSpace Q.A.left := fun Q =>
    have := prop Q; quasiSeparatedSpace_of_quasiSeparated Q.A.hom
  have := prop P; have := prop P'; have := cpt P; have := cpt P'; have := qs P; have := qs P'
  have hi : ∀ e, (β e).hom.left ≫ (β e).inv.left = 𝟙 _ := fun e => by rw [← Over.comp_left, Iso.hom_inv_id]; rfl
  have ih : ∀ e, (β e).inv.left ≫ (β e).hom.left = 𝟙 _ := fun e => by rw [← Over.comp_left, Iso.inv_hom_id]; rfl
  have hβ' : ∀ e, thickMap R I e P.A ≫ (β (e + 1)).inv.left = (β e).inv.left ≫ thickMap R I e P'.A := fun e => by
    have : (β e).inv.left ≫ (thickMap R I e P'.A ≫ (β (e + 1)).hom.left) ≫ (β (e + 1)).inv.left =
        (β e).inv.left ≫ ((β e).hom.left ≫ thickMap R I e P.A) ≫ (β (e + 1)).inv.left := by rw [hβ]
    rw [Category.assoc, hi, Category.comp_id, Category.assoc, ← Category.assoc (β e).inv.left, ih,
      Category.id_comp] at this
    exact this.symm
  have eA : ∀ e, (β e).inv.left ≫ (β e).hom.left ≫ (fstG I e P.A).left = (fstG I e P.A).left := fun e => by
    rw [← Category.assoc, ih, Category.id_comp]
  have eB : ∀ e, (β e).hom.left ≫ (β e).inv.left ≫ (fstG I e P'.A).left = (fstG I e P'.A).left := fun e => by
    rw [← Category.assoc, hi, Category.id_comp]
  choose u hu hu' using fun e => exists_swap _ _ (v e) (hv e) (β e).inv.left (fstG I e P.A).left
    ((β e).inv.left ≫ (fstG I e P'.A).left) (eA e) rfl
  let Rl : ∀ n : ℕ, H0 P'.L n → H0 P.L n → Prop := fun n a b =>
    Rel (T := fun e => (thickObj R I e P'.A).left) (fun e => (β e).hom.left ≫ (fstG I e P.A).left)
      (fun e => (fstG I e P'.A).left) v a b
  have E₁ : ∀ n, 1 ≤ n → ∀ b, ∃! a, Rl n a b := fun n hn b =>
    existsUnique_rel I hS P' P.isLB _ v hv
      (fun e => by rw [← Category.assoc, hβ, Category.assoc, thickMap_fstG]) hc hn b
  have E₂ : ∀ n, 1 ≤ n → ∀ a, ∃! b, Rl n a b := fun n hn a => by
    have H := existsUnique_rel I hS P P'.isLB (fun e => (β e).inv.left ≫ (fstG I e P'.A).left) u hu
      (fun e => by rw [← Category.assoc, hβ', Category.assoc, thickMap_fstG]) (fun e Z r z j' j hj' hj => by
        have e₁ : (r ≫ thickMap R I e P.A) ≫ (fstG I (e + 1) P.A).left = r ≫ (fstG I e P.A).left := by
          rw [Category.assoc, thickMap_fstG]
        have e₂ : (r ≫ thickMap R I e P.A) ≫ (β (e + 1)).inv.left ≫ (fstG I (e + 1) P'.A).left =
            r ≫ (β e).inv.left ≫ (fstG I e P'.A).left := by
          rw [Category.assoc, ← Category.assoc (thickMap R I e P.A), hβ', Category.assoc, thickMap_fstG]
        rw [hu' (e + 1) Z _ z j j' ((congrArg (fun q : Z ⟶ P.A.left => q z ∈ P.L.U j) e₁).mpr hj)
          ((congrArg (fun q : Z ⟶ P'.A.left => q z ∈ P'.L.U j') e₂).mpr hj'), hu' e Z r z j j' hj hj',
          Category.assoc, hβ', ← Category.assoc]
        exact congrArg (·⁻¹) (hc e Z (r ≫ (β e).inv.left) z j j'
          ((congrArg (fun q : Z ⟶ P.A.left => q z ∈ P.L.U j) (congrArg (r ≫ ·) (eA e))).mpr hj) hj')) hn a
    refine (existsUnique_congr fun b => ⟨fun h e Z r z j j' hj hj' => ?_, fun h e Z r z j' j hj' hj => ?_⟩).1 H
    · have m' := (congrArg (fun q : Z ⟶ P'.A.left => q z ∈ P'.L.U j') (congrArg (r ≫ ·) (eB e))).mpr hj'
      have := h e Z (r ≫ (β e).hom.left) z j' j m' hj
      rw [hu' e Z (r ≫ (β e).hom.left) z j j' hj m'] at this
      simp only [Category.assoc] at this
      rw [eB, hi, Category.comp_id] at this
      beta_reduce
      rw [this, ← _root_.mul_assoc, ← mul_pow, Units.mul_inv, one_pow, _root_.one_mul]
    · have m := (congrArg (fun q : Z ⟶ P.A.left => q z ∈ P.L.U j) (congrArg (r ≫ ·) (eA e))).mpr hj
      have := h e Z (r ≫ (β e).inv.left) z j j' m hj'
      simp only [Category.assoc] at this
      rw [eA] at this
      beta_reduce
      rw [hu' e Z r z j j' hj hj', this, ← _root_.mul_assoc, ← mul_pow, Units.inv_mul, one_pow, _root_.one_mul]
  obtain ⟨θ, hθ⟩ : ∃ θ : ∀ n : ℕ, 1 ≤ n → (H0 P'.L n ≃ H0 P.L n), ∀ n hn a, Rl n a (θ n hn a) := by
    refine ⟨fun n hn => ⟨fun a => (E₂ n hn a).exists.choose, fun b => (E₁ n hn b).exists.choose, fun a => ?_,
      fun b => ?_⟩, fun n hn a => (E₂ n hn a).exists.choose_spec⟩
    · exact (E₁ n hn _).unique (E₁ n hn _).exists.choose_spec (E₂ n hn a).exists.choose_spec
    · exact (E₂ n hn _).unique (E₂ n hn _).exists.choose_spec (E₁ n hn b).exists.choose_spec
  have hbase : ∀ e, ((β e).hom.left ≫ (fstG I e P.A).left) ≫ P.A.hom = (fstG I e P'.A).left ≫ P'.A.hom := fun e => by
    rw [Category.assoc, fstG_hom, fstG_hom, ← Category.assoc, Over.w]
  have hlin : ∀ (n : ℕ) (hn : 1 ≤ n) (c : R) (a b d : H0 P'.L n),
      (∀ j, d.f j = a.f j + resTop _ (scal P'.A.hom c) * b.f j) →
      ∀ j, (θ n hn d).f j = (θ n hn a).f j + resTop _ (scal P.A.hom c) * (θ n hn b).f j := by
    intro n hn c a b d h
    have : Rl n d (DVR.SecOps.secAdd (θ n hn a) (DVR.SecOps.secScale (scal P.A.hom c) (θ n hn b))) := by
      intro e Z r z j j' hj hj'
      rw [vl_add_scale (a := θ n hn a) (b := θ n hn b) (c := scal P.A.hom c) (fun _ => rfl) _ z hj,
        vl_add_scale h _ z hj', hθ n hn a e Z r z j j' hj hj', hθ n hn b e Z r z j j' hj hj', gs_scal, gs_scal,
        Category.assoc r, Category.assoc r, hbase]
      ring
    rw [(E₂ n hn d).unique (hθ n hn d) this]
    exact fun _ => rfl
  have hmul : ∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : H0 P'.L n) (b : H0 P'.L m) (d : H0 P'.L (n + m)),
      (∀ j : Fin 1 → P'.L.ι, (show Γ(P'.A.left, ch P'.L j) from d.f j) =
        (show Γ(P'.A.left, ch P'.L j) from a.f j) * (show Γ(P'.A.left, ch P'.L j) from b.f j)) →
      ∀ j : Fin 1 → P.L.ι, (show Γ(P.A.left, ch P.L j) from (θ (n + m) (hn.trans (Nat.le_add_right n m)) d).f j) =
        (show Γ(P.A.left, ch P.L j) from (θ n hn a).f j) * (show Γ(P.A.left, ch P.L j) from (θ m hm b).f j) := by
    intro n m hn hm a b d h
    obtain ⟨d', hd'⟩ := exists_mul (θ n hn a) (θ m hm b)
    have : Rl (n + m) d d' := by
      intro e Z r z j j' hj hj'
      rw [vl_mul hd' _ z hj, vl_mul h _ z hj', hθ n hn a e Z r z j j' hj hj', hθ m hm b e Z r z j j' hj hj']
      ring
    rw [(E₂ _ (hn.trans (Nat.le_add_right n m)) d).unique (hθ _ _ d) this]
    exact hd'
  have h4 : 1 ≤ 4 := by norm_num
  obtain ⟨κ, t, ht, hta⟩ := exists_cover hA P 4 le_rfl
  obtain ⟨κ', s, hs, hsa⟩ := exists_cover hA P' 4 le_rfl
  obtain ⟨κ'', s₅, hs₅, -⟩ := exists_cover hA P' (4 + 1) (by norm_num)
  have mt : ∀ x, ∃ i, x ∈ nonzeroLocus (t i) := fun x => Opens.mem_iSup.1 (by rw [ht]; trivial)
  have ms : ∀ x, ∃ i, x ∈ nonzeroLocus (s i) := fun x => Opens.mem_iSup.1 (by rw [hs]; trivial)
  have ms₅ : ∀ x, ∃ i, x ∈ nonzeroLocus (s₅ i) := fun x => Opens.mem_iSup.1 (by rw [hs₅]; trivial)
  choose d hd using fun p : κ' × κ => exists_mul (s p.1) ((θ 4 h4).symm (t p.2))
  have l' := fun p => locus_mul P'.isLB (hd p)
  have l : ∀ p, nonzeroLocus (θ (4 + 4) (h4.trans (Nat.le_add_right 4 4)) (d p)) =
      nonzeroLocus (θ 4 h4 (s p.1)) ⊓ nonzeroLocus (t p.2) := fun p => by
    rw [locus_mul P.isLB (hmul 4 4 h4 h4 _ _ _ (hd p)), Equiv.apply_symm_apply]
  have mem : ∀ z, ∃ p, (fstG I 0 P'.A).left z ∈ nonzeroLocus (d p) := fun z => by
    obtain ⟨i, hi⟩ := ms ((fstG I 0 P'.A).left z)
    obtain ⟨k, hk⟩ := mt (((β 0).hom.left ≫ (fstG I 0 P.A).left) z)
    refine ⟨(i, k), (l' _).ge ⟨hi, (Rel.mem_iff P.isLB P'.isLB (hθ 4 h4 _) 0 z).1 ?_⟩⟩
    rw [Equiv.apply_symm_apply]
    exact hk
  obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.exists_iso_of_sectionRing_equiv_alt R P.A P'.A P.L P'.L P.isLB P'.isLB θ hlin hmul
    ⟨4 + 4, h4.trans (Nat.le_add_right 4 4), κ' × κ, d,
      eq_top_of_thick I P'.A _ fun z => Opens.mem_iSup.2 (mem z),
      eq_top_of_thick I P.A _ fun z => by
        obtain ⟨p, hp⟩ := mem ((β 0).inv.left z)
        have := (Rel.mem_iff P.isLB P'.isLB (hθ _ (h4.trans (Nat.le_add_right 4 4)) (d p)) 0 _).2 hp
        exact Opens.mem_iSup.2 ⟨p, (congrArg (fun q : (thickObj R I 0 P.A).left ⟶ P.A.left => q z ∈ _) (eA 0)).mp this⟩,
      fun p => ⟨by
        rw [l', inf_comm]; exact isAffineOpen_nonzeroLocus_inf (LB.isLB_linComb P'.isLB _ _) _ (hsa _), by
        rw [l]; exact isAffineOpen_nonzeroLocus_inf (LB.isLB_linComb P.isLB _ _) _ (hta _)⟩⟩
  obtain ⟨w, hw, H⟩ := GlobalTheory.exists_iso_of_sectionRing R P.A P'.A P.L P'.L P.isLB P'.isLB θ hlin hmul Ψ.hom.left hΨ
    fun x => by
      obtain ⟨i, hi⟩ := ms x
      obtain ⟨k, hk⟩ := ms₅ x
      exact ⟨4, h4, s i, s₅ k, hi, hk⟩
  have H' : ∀ (n : ℕ) (hn : 1 ≤ n) (a : H0 P'.L n) (Z : Scheme.{0}) (r : Z ⟶ P'.A.left) (z : Z) (j : P.L.ι)
      (j' : P'.L.ι), Ψ.hom.left (r z) ∈ P.L.U j → r z ∈ P'.L.U j' →
      vl (θ n hn a) (r ≫ Ψ.hom.left) z (fun _ => j) = (gw w r z j j').val ^ n * vl a r z (fun _ => j') := by
    intro n hn a Z r z j j' hj hj'
    refine (H n hn a Z r z (fun _ => j) (fun _ => j') (fun _ => hj) (fun _ => hj')).trans ?_
    rw [Fin.prod_univ_one, Category.comp_id, zpow_natCast, Units.val_pow_eq_pow_val]
  refine ⟨Ψ, w, hw, fun e => ?_⟩
  have key : (β e).hom.left ≫ (fstG I e P.A).left = (fstG I e P'.A).left ≫ Ψ.hom.left := by
    obtain ⟨y, hy, hy'⟩ := exists_swap _ _ (v e) (hv e) (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _)
    obtain ⟨y', T⟩ := exists_comp P'.isLB w y ((isGen_iff w).1 hw) ((isGen_iff y).1 hy) P.isLB
      (LB.isLB_pull P.isLB _)
    refine hom_ext_of_sec_pull_eq _ _ P.L P.isLB ⟨4, h4, κ, t, ht, hta⟩ _ _ y'
      ((isGen_iff y').2 (T.pgen_comp P'.isLB ((isGen_iff w).1 hw) ((isGen_iff y).1 hy))) fun n hn b z j j' hj hj' => ?_
    obtain ⟨a, rfl⟩ := (θ n hn).surjective b
    obtain ⟨k, hk⟩ := exists_chart P'.isLB ((fstG I e P'.A).left z)
    have h₁ := H' n hn a _ (fstG I e P'.A).left z j k hj hk
    have h₂ := hθ n hn a e _ (𝟙 ((Over.map (thick R I e)).obj (thickObj R I e P'.A)).left) z j' k hj' hk
    have h₃ := T _ (𝟙 _) z j k (fun _ => j') hj hk (mem_pull.2 hj')
    rw [hy' _ (𝟙 _) z j' k hj' hk] at h₃
    simp only [Category.id_comp] at h₂ h₃
    refine h₁.trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg (fun t => (t ^ n).val) h₃) h₂).symm)
    rw [Units.val_pow_eq_pow_val, ← _root_.mul_assoc, ← mul_pow, ← Units.val_mul, inv_mul_cancel_right]
  refine ⟨key.symm, fun Z r z j j' hj hj' => ?_⟩
  have hj₂ := (congrArg (fun q : (thickObj R I e P'.A).left ⟶ P.A.left => q (r z) ∈ P.L.U j) key).mp hj
  have pw : ∀ (n : ℕ) (hn : 1 ≤ n) (a : H0 P'.L n), (fstG I e P'.A).left (r z) ∈ nonzeroLocus a →
      gw w (r ≫ (fstG I e P'.A).left) z j j' ^ n = gw (v e) r z j (fun _ => j') ^ n := fun n hn a ha => by
    have h₁ := H' n hn a _ (r ≫ (fstG I e P'.A).left) z j j' hj₂ hj'
    have h₂ := hθ n hn a e _ r z j j' hj hj'
    rw [Category.assoc, ← key] at h₁
    exact Units.ext (((mem_iff_isUnit a (r ≫ (fstG I e P'.A).left) z (j := fun _ => j') hj').1 ha).mul_right_cancel
      (h₁.symm.trans h₂))
  obtain ⟨i, hi⟩ := ms ((fstG I e P'.A).left (r z))
  obtain ⟨k, hk⟩ := ms₅ ((fstG I e P'.A).left (r z))
  have a₅ := pw (4 + 1) (Nat.le_add_left 1 4) _ hk
  rw [pow_succ, pow_succ _ 4, pw 4 h4 _ hi] at a₅
  exact mul_left_cancel a₅
