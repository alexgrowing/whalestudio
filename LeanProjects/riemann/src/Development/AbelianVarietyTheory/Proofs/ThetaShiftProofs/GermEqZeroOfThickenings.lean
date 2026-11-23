import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PGAppEqZeroIff
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtOfSucc
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSub
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValueAtUnitSection
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalValue

section Values

variable {A A' : Type} [CommRing A] [CommRing A'] {X Y : Scheme.{0}}

theorem toStkA_valR_eq_gs (x : Sp A ⟶ X) (V : X.Opens) (z : Sp A) (ht : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, V)) :
    toStkA z (valR x V a) = gs x z V a := by
  rw [valR, dif_pos ht, gs_eq x z V (ht trivial)]
  show ((Sp A).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp A).presheaf (homOfLE ht) z trivial _

theorem top_le_comp {x : Sp A ⟶ X} {V : X.Opens} (ht : ⊤ ≤ x ⁻¹ᵁ V) (r : Sp A' ⟶ Sp A) : ⊤ ≤ (r ≫ x) ⁻¹ᵁ V :=
  fun y _ => ht (show r y ∈ (⊤ : (Sp A).Opens) from trivial)

theorem valR_spMap (ρ : A →+* A') (x : Sp A ⟶ X) (V : X.Opens) (ht : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, V)) :
    valR (spMap ρ ≫ x) V a = ρ (valR x V a) := by
  rw [valR, valR, dif_pos ht, dif_pos (top_le_comp ht _),
    ← Scheme.Hom.appLE_comp_appLE (spMap ρ) x V ⊤ ⊤ ht le_top]
  have e := congrArg (fun q => q.hom ((x.appLE V ⊤ ht).hom a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ρ))
  refine Eq.trans ?_ e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  congr 2

theorem toStkA_map_valR (ρ : A →+* A') (x : Sp A ⟶ X) (V : X.Opens) (z : Sp A') (ht : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, V)) :
    toStkA z (ρ (valR x V a)) = gs (spMap ρ ≫ x) z V a := by
  rw [← valR_spMap ρ x V ht, toStkA_valR_eq_gs _ V z (top_le_comp ht _)]

theorem isUnit_valR (x : Sp A ⟶ X) (V : X.Opens) (ht : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, V)ˣ) : IsUnit (valR x V a.val) := by
  rw [valR, dif_pos ht]
  exact (a.isUnit.map _).map _

theorem valR_fromSpecStalk (x : X) (V : X.Opens) (hx : x ∈ V) (a : Γ(X, V)) :
    valR (A := X.presheaf.stalk x) (X.fromSpecStalk x) V a = (X.presheaf.germ V x hx).hom a := by
  have ht : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ V := (top_le_iff_cpt (A := X.presheaf.stalk x) _ V).2 (by
    rw [show X.fromSpecStalk x (cpt (X.presheaf.stalk x)) = x from Scheme.fromSpecStalk_closedPoint]; exact hx)
  refine (dif_pos ht).trans ?_
  have : (X.fromSpecStalk x).appLE V ⊤ ht ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom = X.presheaf.germ V x hx := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
    simp only [Category.assoc]
    have e : (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE (le_top : X.fromSpecStalk x ⁻¹ᵁ V ≤ ⊤)).op ≫
        (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE ht).op = 𝟙 _ := by
      rw [← Functor.map_comp]; exact CategoryTheory.Functor.map_id _ _
    rw [reassoc_of% e, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun q => q.hom a) this

end Values

section Krull

variable {R : Type} [CommRing R] (I : Ideal R)

theorem exists_lift_thick (H : Over (Sp R)) {S : Type} [CommRing S] (φ : R →+* S) (x : Sp S ⟶ H.left)
    (hx : x ≫ H.hom = spMap φ) (e : ℕ) :
    ∃ xe : Sp (S ⧸ I.map φ ^ (e + 1)) ⟶ (thickObj R I e H).left,
      xe ≫ (fstG I e H).left = spMap (Ideal.Quotient.mk _) ≫ x :=
  ⟨pullback.lift (spMap (Ideal.Quotient.mk _) ≫ x)
    (spMap (Ideal.quotientMap (I.map φ ^ (e + 1)) φ (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)))
    (by
      rw [Category.assoc, hx, ← Spec.map_comp, ← Spec.map_comp]
      rfl), pullback.lift_fst _ _ _⟩

theorem germ_eq_zero_of_thickenings (H : Over (Sp R)) [IsLocallyNoetherian H.left] (V : H.left.Opens)
    (a : Γ(H.left, V)) (h : ∀ e, ((fstG I e H).left.app V).hom a = 0) (y : H.left) (hy : y ∈ V)
    (hI : I ≤ (H.hom y).asIdeal) : (H.left.presheaf.germ V y hy).hom a = 0 := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (H.left.fromSpecStalk y ≫ H.hom)
  have hc : H.left.fromSpecStalk y (cpt (H.left.presheaf.stalk y)) = y := Scheme.fromSpecStalk_closedPoint
  have ht : ⊤ ≤ H.left.fromSpecStalk y ⁻¹ᵁ V := (top_le_iff_cpt (A := H.left.presheaf.stalk y) _ V).2 (by
    rw [hc]; exact hy)
  have hJ : I.map φ.hom ≠ ⊤ := by
    have h₁ : H.hom y = Spec.map φ (cpt (H.left.presheaf.stalk y)) := by
      rw [hφ, Scheme.Hom.comp_apply, hc]
    rw [h₁] at hI
    exact fun h₂ => (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (top_le_iff.1 (h₂ ▸ (Ideal.map_le_iff_le_comap.2 hI)))
  rw [← valR_fromSpecStalk y V hy, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ hJ, Ideal.mem_iInf]
  intro e
  refine Ideal.pow_le_pow_right (Nat.le_succ e) ?_
  obtain ⟨xe, hxe⟩ := exists_lift_thick I H φ.hom (H.left.fromSpecStalk y) hφ.symm e
  have := isLocalRing_quotient_pow hJ e
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply toStkA_injective
  have hm : (fstG I e H).left (xe (cpt _)) ∈ V := by
    rw [← Scheme.Hom.comp_apply, hxe]; exact top_le_comp ht _ trivial
  refine (toStkA_map_valR (A := H.left.presheaf.stalk y) _ _ V _ ht a).trans (Eq.trans ?_ (map_zero _).symm)
  refine (congrArg (fun q => gs q _ V a) hxe).symm.trans ((gs_pull _ _ _ _ hm _).symm.trans ?_)
  exact (congrArg (gs xe _ _) (h e)).trans (gs_zero _ _ _ hm)

theorem sec_eq_zero_of_thickenings [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) (H : Over (Sp R))
    [IsProper H.hom] {N : LB H.left} (s : LB.Sec N) (hN : ∀ y, ∃ i, y ∈ N.U i)
    (h : ∀ e j, ((fstG I e H).left.app _).hom (s.f j) = 0) (j : N.ι) : s.f j = 0 := by
  have : IsLocallyNoetherian H.left := LocallyOfFiniteType.isLocallyNoetherian H.hom
  let Z : Set H.left := {y | ∃ i, ∃ hy : y ∈ N.U i, (H.left.presheaf.germ _ y hy).hom (s.f i) = 0}
  have hZ : IsOpen Z := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨i, hy, e⟩
    obtain ⟨W, hW, iU, iV, e'⟩ := TopCat.Presheaf.germ_eq H.left.presheaf y hy hy (s.f i) 0
      (e.trans (map_zero _).symm)
    refine ⟨W, fun y' hy' => ⟨i, iU.le hy', ?_⟩, W.isOpen, hW⟩
    have e₁ := TopCat.Presheaf.germ_res_apply H.left.presheaf iU y' hy' (s.f i)
    have e₂ := TopCat.Presheaf.germ_res_apply H.left.presheaf iV y' hy' 0
    exact e₁.symm.trans ((congrArg _ e').trans (e₂.trans (map_zero _)))
  have hall : ∀ y, y ∈ Z := by
    by_contra hne
    push Not at hne
    obtain ⟨y, hy⟩ := hne
    have hc : IsClosed (H.hom '' Zᶜ) := H.hom.isClosedMap _ hZ.isClosed_compl
    obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal (H.hom y).asIdeal (H.hom y).2.ne_top
    let m' : Sp R := ⟨m, hm.isPrime⟩
    have h₂ : H.hom y ⤳ m' := (PrimeSpectrum.le_iff_specializes (H.hom y) m').1 hpm
    obtain ⟨y', hy', e⟩ := h₂.mem_closed hc ⟨y, hy, rfl⟩
    obtain ⟨i, hi⟩ := hN y'
    refine hy' ⟨i, hi, germ_eq_zero_of_thickenings I H _ _ (fun e => h e i) y' hi ?_⟩
    rw [e]
    exact hI.trans (sInf_le ⟨bot_le, hm⟩)
  refine fn_ext fun y hy => ?_
  obtain ⟨i, hi, e⟩ := hall y
  have hm : (𝟙 H.left : H.left ⟶ H.left) y ∈ N.U j ⊓ N.U i := ⟨hy, hi⟩
  have e' : gs (𝟙 H.left) y (N.U i) (s.f i) = 0 := (gs_eq _ y _ hi _).trans e
  refine (gs_res _ y _ hm _).symm.trans ((congrArg (gs _ y _) (s.compat j i)).trans ((gs_mul _ y _ hm _ _).trans ?_))
  rw [gs_res _ y _ hm, e', mul_zero, gs_zero _ _ _ hy]

end Krull

section Formal

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  {S : Type} [CommRing S] {s : Sp S ⟶ Sp R}

abbrev basePt (g : GtPt D.toPre (Over.mk s)) : Sp S ⟶ D.toPre.P.A.left := g.b.left

abbrev coordφ (g : GtPt D.toPre (Over.mk s)) (α : D.toPre.X) : Fin 4 → (Sp S ⟶ D.toPre.P.A.left) :=
  D.toPre.gtφT (Over.mk s) g.b α

abbrev coord (g : GtPt D.toPre (Over.mk s)) (α : D.toPre.X) :
    LB.Gen (LB.LinComb D.toPre.P.L (coordφ g α) DegPre.gtε) := g.s α

def HasCoords (g : GtPt D.toPre (Over.mk s)) (x : Sp S ⟶ G.left) (e : ℕ) {Z : Scheme.{0}} (r : Z ⟶ Sp S)
    (xe : Z ⟶ (thickObj R I e G).left) : Prop :=
  xe ≫ (fstG I e G).left = r ≫ x ∧ xe ≫ (U.gt e).pG.left = r ≫ basePt g ∧
    ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe)
      (LB.pullGen D.toPre.P.L _ _ (coord g χ) r)

def IsFormalPt (J : Ideal S) (g : GtPt D.toPre (Over.mk s)) (x : Sp S ⟶ G.left) : Prop :=
  ∀ e, ∃ xe, HasCoords U g x e (thick S J e) xe

def wVal (e : ℕ) {T : Type} [CommRing T] (xe : Sp T ⟶ (thickObj R I e G).left) (jL : U.LG.L.ι)
    (jM : D.toPre.P.L.ι) : T :=
  valR xe ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => jM) ⊓ (U.LG.L.pull (fstG I e G).left).U (fun _ => jL))
    ((U.w e).s (fun _ => jM, fun _ => jL)).val

def secVal {k : ℕ} (σ : H0 U.LG.L k) (x : Sp S ⟶ G.left) (jL : U.LG.L.ι) : S :=
  valR x (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL))

def famVal (g : GtPt D.toPre (Over.mk s)) {k : ℕ} {α : D.toPre.X} (t : D.toPre.SecB k α)
    (jf : Fin 4 → D.toPre.P.L.ι) : S :=
  valR (basePt g) (LB.wchart D.toPre.P.L (D.toPre.famφB α) jf) (t.f jf)

def coordVal (g : GtPt D.toPre (Over.mk s)) (α : D.toPre.X) (jt : Fin 4 → D.toPre.P.L.ι) : S :=
  valR (𝟙 (Sp S)) (LB.wchart D.toPre.P.L (coordφ g α) jt) ((coord g α).s jt).val

def CohCharts (g : GtPt D.toPre (Over.mk s)) (α : D.toPre.X) (jM : D.toPre.P.L.ι)
    (jf jt : Fin 4 → D.toPre.P.L.ι) : Prop :=
  ⊤ ≤ basePt g ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB α) jf ∧ ⊤ ≤ LB.wchart D.toPre.P.L (coordφ g α) jt ∧
    CohAll D.toPre.P.L
      (Sum.elim (fun _ : PUnit.{1} => basePt g) (Sum.elim (fun a => basePt g ≫ D.toPre.famφB α a) (coordφ g α)))
      (Sum.elim (fun _ => jM) (Sum.elim jf jt))

def IsTau (J : Ideal S) (x : Sp S ⟶ G.left) (jL : U.LG.L.ι) (jM : D.toPre.P.L.ι) (τ : S) : Prop :=
  ∀ (e : ℕ) (xe : Sp (S ⧸ J ^ (e + 1)) ⟶ (thickObj R I e G).left), xe ≫ (fstG I e G).left = thick S J e ≫ x →
    Ideal.Quotient.mk _ τ * wVal U e xe jL jM = 1

open Classical in

def tau (J : Ideal S) (x : Sp S ⟶ G.left) (jL : U.LG.L.ι) (jM : D.toPre.P.L.ι) : Sˣ :=
  if h : ∃ τ : Sˣ, IsTau U J x jL jM τ then h.choose else 1

variable {U} {g : GtPt D.toPre (Over.mk s)} {x : Sp S ⟶ G.left}

omit [IsDomain R] [GrpObj G] [IsCommMonObj G] in
theorem fstG_mono (e : ℕ) : Mono (fstG I e G).left :=
  have := thick_mono R I e
  inferInstanceAs (Mono (pullback.fst G.hom (thick R I e)))

theorem HasCoords.val_eq {e : ℕ} {Z Z' : Scheme.{0}} {r : Z ⟶ Sp S} {xe : Z ⟶ (thickObj R I e G).left}
    (h : HasCoords U g x e r xe) (χ : D.toPre.X) (p : Z' ⟶ Z) {z : Z'} {J} (hJ : Good D.toPre.P.L z J) :
    val (tG U e χ) (p ≫ xe) z J = val (coord g χ) (p ≫ r) z J :=
  (val_pull hJ _ _ _).symm.trans ((val_corr hJ (h.2.2 χ) p).trans (val_pull hJ _ _ _))

theorem HasCoords.comp {e : ℕ} {Z Z' : Scheme.{0}} {r : Z ⟶ Sp S} {xe : Z ⟶ (thickObj R I e G).left}
    (h : HasCoords U g x e r xe) (p : Z' ⟶ Z) : HasCoords U g x e (p ≫ r) (p ≫ xe) := by
  refine ⟨by rw [Category.assoc, h.1, Category.assoc], by rw [Category.assoc, h.2.1, Category.assoc],
    fun χ => corr_of_val D.toPre.P.isLB fun y J hJ => ?_⟩
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
  rw [Category.id_comp, Category.id_comp]
  exact h.val_eq χ p hJ

theorem isFormalPt_of_surjective (J : Ideal S)
    (h : ∀ e, ∃ (T : Type) (_ : CommRing T) (ρ : S →+* T) (xe : Sp T ⟶ (thickObj R I e G).left),
      Function.Surjective ρ ∧ RingHom.ker ρ ≤ J ^ (e + 1) ∧ HasCoords U g x e (spMap ρ) xe) :
    IsFormalPt U J g x := by
  intro e
  obtain ⟨T, _, ρ, xe, hs, hk, h⟩ := h e
  let π : T →+* S ⧸ J ^ (e + 1) := ρ.liftOfSurjective hs ⟨Ideal.Quotient.mk _, by rwa [Ideal.mk_ker]⟩
  have hπ : spMap π ≫ spMap ρ = thick S J e := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (ρ.liftOfSurjective_comp hs _)
  exact ⟨_, hπ ▸ h.comp (spMap π)⟩

theorem isFormalPt_of_forall {φ : R →+* S} (hx : x ≫ G.hom = spMap φ)
    (h : ∀ (e : ℕ) (xe : Sp (S ⧸ I.map φ ^ (e + 1)) ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = thick S (I.map φ) e ≫ x → HasCoords U g x e (thick S (I.map φ) e) xe) :
    IsFormalPt U (I.map φ) g x := fun e =>
  (exists_lift_thick I G φ x hx e).imp fun xe hxe => h e xe hxe

theorem IsFormalPt.hasCoords {J : Ideal S} (h : IsFormalPt U J g x) {e : ℕ} {T : Type} [CommRing T] (ρ : S →+* T)
    (hρ : J ^ (e + 1) ≤ RingHom.ker ρ) {xe : Sp T ⟶ (thickObj R I e G).left}
    (hxe : xe ≫ (fstG I e G).left = spMap ρ ≫ x) : HasCoords U g x e (spMap ρ) xe := by
  obtain ⟨y, hy⟩ := h e
  have hπ : spMap (Ideal.Quotient.lift _ ρ hρ) ≫ thick S J e = spMap ρ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have H := hπ ▸ hy.comp (spMap (Ideal.Quotient.lift _ ρ hρ))
  have := fstG_mono (I := I) (G := G) e
  rwa [(cancel_mono _).1 (hxe.trans H.1.symm)]

theorem exists_cohCharts [IsLocalRing S] (g : GtPt D.toPre (Over.mk s)) (jM : D.toPre.P.L.ι)
    (hM : ⊤ ≤ basePt g ⁻¹ᵁ D.toPre.P.L.U jM) (α : D.toPre.X) : ∃ jf jt, CohCharts g α jM jf jt := by
  obtain ⟨J, hJ, e⟩ := exists_good D.toPre.P.L D.toPre.P.isLB (cpt S) (fun _ : PUnit.{1} => basePt g) (fun _ => jM)
    (fun _ _ _ => rfl) (fun _ => hM trivial)
  refine ⟨fun a => J (basePt g ≫ D.toPre.famφB α a), fun a => J (coordφ g α a),
    (top_le_iff_cpt _ _).2 (hJ.mem _ _), (top_le_iff_cpt (𝟙 (Sp S)) (LB.wchart D.toPre.P.L (coordφ g α) fun a => J (coordφ g α a))).2
      (Set.mem_iInter.2 fun a => hJ _), ?_⟩
  have c : ∀ a, Sum.elim (fun _ : PUnit.{1} => jM) (Sum.elim (fun a => J (basePt g ≫ D.toPre.famφB α a))
      (fun a => J (coordφ g α a))) a = J (Sum.elim (fun _ : PUnit.{1} => basePt g)
        (Sum.elim (fun a => basePt g ≫ D.toPre.famφB α a) (coordφ g α)) a) := by
    rintro (a | a | a)
    exacts [(e a).symm, rfl, rfl]
  exact fun a b hab => (c a).trans ((congrArg J hab).trans (c b).symm)

theorem basePt_famφB (g : GtPt D.toPre (Over.mk s)) (α : D.toPre.X) :
    basePt g ≫ D.toPre.famφB α 0 = basePt g ∧ basePt g ≫ D.toPre.famφB α 1 = coordφ g α 0 ∧
      basePt g ≫ D.toPre.famφB α 2 = coordφ g α 1 ∧ basePt g ≫ D.toPre.famφB α 3 = coordφ g α 3 := by
  have u : ∀ c : 𝟙_ _ ⟶ D.toPre.P.A, g.b ≫ toUnit _ ≫ c = toUnit _ ≫ c := fun c => by
    rw [← Category.assoc, comp_toUnit]
  refine ⟨Category.comp_id _, ?_, congrArg Over.Hom.left (u _), congrArg Over.Hom.left (u _)⟩
  have : g.b ≫ ((𝟙 D.toPre.P.A) * (toUnit _ ≫ D.toPre.c α)) = (toUnit _ ≫ D.toPre.c α) * g.b := by
    rw [MonObj.comp_mul, u, Category.comp_id, _root_.mul_comm]
  exact congrArg Over.Hom.left this

theorem gs_mul_gm_eq {α : D.toPre.X} {jM : D.toPre.P.L.ι} {jf jt : Fin 4 → D.toPre.P.L.ι}
    (hc : CohCharts g α jM jf jt) {k : ℕ} (t : D.toPre.SecB k α) {Z : Scheme.{0}} (r : Z ⟶ Sp S) {z : Z} {J}
    (hJ : Good D.toPre.P.L z J) (hM : J (r ≫ basePt g) = jM) :
    gs (r ≫ basePt g) z (LB.wchart D.toPre.P.L (D.toPre.famφB α) jf) (t.f jf) *
        (gm r z (LB.wchart D.toPre.P.L (coordφ g α) jt) ((coord g α).s jt)).val =
      sval t (r ≫ basePt g) z J * (val (coord g α) r z J).val := by
  obtain ⟨h₁, h₂, h₃⟩ := hc
  obtain ⟨b₀, b₁, b₂, b₃⟩ := basePt_famφB g α
  have f₀ : jf 0 = jM := h₃ (.inr (.inl 0)) (.inl PUnit.unit) b₀
  have f₁ : jf 1 = jt 0 := h₃ (.inr (.inl 1)) (.inr (.inr 0)) b₁
  have f₂ : jf 2 = jt 1 := h₃ (.inr (.inl 2)) (.inr (.inr 1)) b₂
  have f₃ : jf 3 = jt 3 := h₃ (.inr (.inl 3)) (.inr (.inr 3)) b₃
  have t₂ : jt 2 = jM := h₃ (.inr (.inr 2)) (.inl PUnit.unit) rfl
  have e₁ := sec_trans t (r ≫ basePt g) z (top_le_comp h₁ (𝟙 _) (show r z ∈ (⊤ : (Sp S).Opens) from trivial))
    (hJ.mem (D.toPre.famφB α) (r ≫ basePt g))
  have e₂ := gen_trans (t := coord g α) (g.isGen α) r z (h₂ (show r z ∈ (⊤ : (Sp S).Opens) from trivial))
    (hJ.mem (coordφ g α) r)
  refine (congrArg₂ (· * ·) e₁ (congrArg Units.val e₂)).trans ?_
  rw [Units.val_mul, _root_.mul_mul_mul_comm, ← Units.val_mul]
  refine (congrArg (· * _) (congrArg Units.val (?_ : _ = (1 : (Z.presheaf.stalk z)ˣ)))).trans (_root_.one_mul _)
  let h : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι → (Z.presheaf.stalk z)ˣ := fun ψ j =>
    gm ψ z (D.toPre.P.L.U j ⊓ D.toPre.P.L.U (J ψ)) (D.toPre.P.L.g j (J ψ))
  have h₀ : h (r ≫ basePt g) jM = 1 := by
    subst hM
    exact gm_self D.toPre.P.isLB _ z (hJ _)
  show (∏ a, h ((r ≫ basePt g) ≫ D.toPre.famφB α a) (jf a) ^ DegPre.famε k a) *
    ∏ a, h (r ≫ coordφ g α a) (jt a) ^ DegPre.gtε a = 1
  simp only [Category.assoc, Fin.prod_univ_four]
  rw [b₀, b₁, b₂, b₃, f₀, f₁, f₂, f₃, t₂, show coordφ g α 2 = basePt g from rfl, h₀]
  show 1 ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) *
    (_ ^ (-1 : ℤ) * _ ^ (1 : ℤ) * 1 ^ (1 : ℤ) * _ ^ (-1 : ℤ)) = _
  simp only [one_zpow, zpow_neg, zpow_one]
  generalize h _ (jt 0) = a
  generalize h _ (jt 1) = b
  generalize h _ (jt 3) = c
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem HasCoords.top_le_chart {e : ℕ} {T : Type} [CommRing T] {r : Sp T ⟶ Sp S}
    {xe : Sp T ⟶ (thickObj R I e G).left} (h : HasCoords U g x e r xe) {jL : U.LG.L.ι} {jM : D.toPre.P.L.ι}
    (hL : ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL) (hM : ⊤ ≤ basePt g ⁻¹ᵁ D.toPre.P.L.U jM) :
    ⊤ ≤ xe ⁻¹ᵁ ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => jM) ⊓
      (U.LG.L.pull (fstG I e G).left).U (fun _ => jL)) := fun z _ =>
  ⟨mem_pull.2 ((congrArg (fun q => q z ∈ D.toPre.P.L.U jM) h.2.1).mpr (top_le_comp hM r trivial)),
    mem_pull.2 ((congrArg (fun q => q z ∈ U.LG.L.U jL) h.1).mpr (top_le_comp hL r trivial))⟩

theorem HasCoords.toStkA_wVal {e : ℕ} {T : Type} [CommRing T] {r : Sp T ⟶ Sp S}
    {xe : Sp T ⟶ (thickObj R I e G).left} (h : HasCoords U g x e r xe) {jL : U.LG.L.ι} {jM : D.toPre.P.L.ι}
    (hL : ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL) (hM : ⊤ ≤ basePt g ⁻¹ᵁ D.toPre.P.L.U jM) (z : Sp T) :
    toStkA z (wVal U e xe jL jM) = (wv U e xe z jM jL).val :=
  toStkA_valR xe _ z (h.top_le_chart hL hM) _

theorem top_le_secChart {jL : U.LG.L.ι} (hL : ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL) :=
  fun _ hz => Set.mem_iInter.2 fun _ => hL hz

variable (U) in

theorem expandsAt_value {e k : ℕ} {σ : H0 U.LG.L k} {f : ∀ α : D.toPre.X, D.toPre.SecB k α}
    (h : U.ExpandsAt e k σ f) : ∃ F : Finset D.toPre.X, ∀ (S : Type) [CommRing S] (s : Sp S ⟶ Sp R)
      (g : GtPt D.toPre (Over.mk s)) (x : Sp S ⟶ G.left) (T : Type) [CommRing T] [IsLocalRing T] (ρ : S →+* T)
      (xe : Sp T ⟶ (thickObj R I e G).left), HasCoords U g x e (spMap ρ) xe →
      (∀ α ∉ F, ∀ jf, ⊤ ≤ basePt g ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB α) jf → ρ (famVal g (f α) jf) = 0) ∧
      ∀ (jL : U.LG.L.ι) (jM : D.toPre.P.L.ι) (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι),
        ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL → ⊤ ≤ basePt g ⁻¹ᵁ D.toPre.P.L.U jM → (∀ α ∈ F, CohCharts g α jM (jf α) (jt α)) →
        wVal U e xe jL jM ^ k * ρ (secVal U σ x jL) = ρ (∑ α ∈ F, famVal g (f α) (jf α) * coordVal g α (jt α)) := by
  obtain ⟨F, hF⟩ := expandsAt_val U e k σ f h
  refine ⟨F, fun S _ s g x T _ _ ρ xe hx => ⟨fun α hα jf hj => ?_, fun jL jM jf jt hL hM hc => ?_⟩⟩
  · choose J hJ using fun ψ : Sp T ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ (cpt T))
    have h₀ := (hF _ xe (cpt T) J hJ).1 α hα
    rw [show xe ≫ pGl U e = spMap ρ ≫ basePt g from hx.2.1] at h₀
    apply toStkA_injective
    refine (toStkA_map_valR ρ _ _ _ hj _).trans ((sec_trans (f α) _ _ (top_le_comp hj _ trivial)
      (Good.mem hJ (D.toPre.famφB α) (spMap ρ ≫ basePt g))).trans ?_)
    exact (congrArg _ h₀).trans ((mul_zero _).trans (map_zero _).symm)
  · obtain ⟨J, hJ, eJ⟩ := exists_good D.toPre.P.L D.toPre.P.isLB (cpt T) (fun _ : PUnit.{1} => spMap ρ ≫ basePt g)
      (fun _ => jM) (fun _ _ _ => rfl) (fun _ => top_le_comp hM _ trivial)
    have eM : J (spMap ρ ≫ basePt g) = jM := eJ PUnit.unit
    have H := (hF _ xe (cpt T) J hJ).2 jL
      ((congrArg (fun q => q (cpt T) ∈ U.LG.L.U jL) hx.1).mpr (top_le_comp hL _ trivial))
    rw [show xe ≫ pGl U e = spMap ρ ≫ basePt g from hx.2.1, show xe ≫ fGl I G e = spMap ρ ≫ x from hx.1, eM] at H
    apply toStkA_injective
    rw [map_mul, map_pow, hx.toStkA_wVal hL hM, map_sum, map_sum]
    refine (congrArg₂ (· * ·) (Units.val_pow_eq_pow_val _ _).symm
      (toStkA_map_valR ρ x _ _ (top_le_secChart hL) _)).trans (H.trans (Finset.sum_congr rfl fun α hα => ?_))
    have hv := hx.val_eq α (𝟙 _) hJ
    rw [Category.id_comp, Category.id_comp] at hv
    rw [hv, ← gs_mul_gm_eq (hc α hα) (f α) (spMap ρ) hJ eM, map_mul, map_mul]
    refine (congrArg₂ (· * ·) (toStkA_map_valR ρ _ _ _ (hc α hα).1 _) ?_).symm
    refine (toStkA_map_valR ρ (𝟙 (Sp S)) (LB.wchart D.toPre.P.L (coordφ g α) (jt α)) _ (hc α hα).2.1 _).trans ?_
    rw [Category.comp_id]
    exact gs_unit _ _ _ ((hc α hα).2.1 (show spMap ρ (cpt T) ∈ (⊤ : (Sp S).Opens) from trivial)) _

theorem exists_limit (J : Ideal S) [IsPrecomplete J S] (v : ∀ e : ℕ, S ⧸ J ^ (e + 1))
    (hv : ∀ e, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) (v (e + 1)) = v e) :
    ∃ a : S, ∀ e, Ideal.Quotient.mk (J ^ (e + 1)) a = v e := by
  choose c hc using fun e => Ideal.Quotient.mk_surjective (v e)
  have h₁ : ∀ e, c (e + 1) - c e ∈ J ^ (e + 1) := fun e => by
    rw [← Ideal.Quotient.eq, hc e, ← hv e, ← hc (e + 1), Ideal.Quotient.factor_mk]
  have h₀ : ∀ m d, c m - c (m + d) ∈ J ^ m := fun m d => by
    induction d with
    | zero => simp
    | succ d ih =>
      have h₂ : c (m + d + 1) - c (m + d) ∈ J ^ m := Ideal.pow_le_pow_right (by omega) (h₁ (m + d))
      have e : c m - c (m + (d + 1)) = (c m - c (m + d)) - (c (m + d + 1) - c (m + d)) := by
        rw [← _root_.add_assoc]; ring
      rw [e]
      exact (J ^ m).sub_mem ih h₂
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' (I := J) c fun {m n} hmn => by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact h₀ m d
  refine ⟨a, fun e => ?_⟩
  have h₂ := ha (e + 1)
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h₂
  rw [← hc e, Ideal.Quotient.eq]
  have e' : a - c e = (c (e + 1) - c e) - (c (e + 1) - a) := by ring
  rw [e']
  exact (J ^ (e + 1)).sub_mem (h₁ e) h₂

theorem eq_of_forall_mk_eq (J : Ideal S) [IsHausdorff J S] {a b : S}
    (h : ∀ e, Ideal.Quotient.mk (J ^ (e + 1)) a = Ideal.Quotient.mk _ b) : a = b := by
  refine sub_eq_zero.1 (IsHausdorff.haus' (I := J) _ fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.Quotient.eq.1 (h n))

theorem exists_unit_limit (J : Ideal S) [IsAdicComplete J S] (v : ∀ e : ℕ, S ⧸ J ^ (e + 1))
    (hv : ∀ e, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) (v (e + 1)) = v e)
    (hu : ∀ e, IsUnit (v e)) : ∃ a : Sˣ, ∀ e, Ideal.Quotient.mk (J ^ (e + 1)) a.val * v e = 1 := by
  choose u hu using hu
  obtain ⟨a, ha⟩ := exists_limit J _ hv
  obtain ⟨b, hb⟩ := exists_limit J (fun e => ((u e)⁻¹).val) fun e => by
    refine Units.eq_inv_of_mul_eq_one_left ?_
    rw [hu e, ← hv e, ← hu (e + 1), ← map_mul, Units.mul_inv, map_one]
  have h₁ : ∀ e, Ideal.Quotient.mk (J ^ (e + 1)) b * v e = 1 := fun e => by
    rw [hb, ← hu, Units.inv_mul]
  have hab : b * a = 1 := eq_of_forall_mk_eq J fun e => by rw [map_mul, ha, h₁, map_one]
  exact ⟨⟨b, a, hab, (_root_.mul_comm _ _).trans hab⟩, h₁⟩

theorem wv_comp_thickMap (e : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι)
    (jL : U.LG.L.ι) (hM : pGl U e (r z) ∈ D.toPre.P.L.U jM) (hL : fGl I G e (r z) ∈ U.LG.L.U jL) :
    wv U (e + 1) (r ≫ thickMap R I e G) z jM jL = wv U e r z jM jL := by
  have hM' : pGl U (e + 1) (thickMap R I e G (r z)) ∈ D.toPre.P.L.U jM :=
    (congrArg (fun g => g (r z) ∈ D.toPre.P.L.U jM) (U.gt_q e)).mpr hM
  have hL' : fGl I G (e + 1) (thickMap R I e G (r z)) ∈ U.LG.L.U jL :=
    (congrArg (fun g => g (r z) ∈ U.LG.L.U jL) (thickMap_comp_fGl I e G)).mpr hL
  have hm : r z ∈ thickMap R I e G ⁻¹ᵁ ((D.toPre.P.L.pull (pGl U (e + 1))).U (fun _ => jM) ⊓
        (U.LG.L.pull (fGl I G (e + 1))).U (fun _ => jL)) ⊓
      ((D.toPre.P.L.pull (pGl U e)).U (fun _ => jM) ⊓ (U.LG.L.pull (fGl I G e)).U (fun _ => jL)) :=
    ⟨⟨mem_pull.2 hM', mem_pull.2 hL'⟩, mem_pull.2 hM, mem_pull.2 hL⟩
  have W := congrArg (gm r z _) (U.w_compat e (fun _ => jM, fun _ => jL) _ inf_le_left inf_le_right)
  exact ((gm_res r z inf_le_left hm _).trans (gm_pull r _ z _ hm.1 _)).symm.trans
    (W.trans (gm_res r z inf_le_right hm _))

section Tau

variable {J : Ideal S} [IsLocalRing S] [IsAdicComplete J S] {jL jL' : U.LG.L.ι} {jM jM' : D.toPre.P.L.ι}

theorem factor_wVal {e : ℕ} {y : Sp (S ⧸ J ^ (e + 1)) ⟶ (thickObj R I e G).left}
    {y' : Sp (S ⧸ J ^ (e + 1 + 1)) ⟶ (thickObj R I (e + 1) G).left} (hy : HasCoords U g x e (thick S J e) y)
    (hy' : HasCoords U g x (e + 1) (thick S J (e + 1)) y') (hL : ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL)
    (hM : ⊤ ≤ basePt g ⁻¹ᵁ D.toPre.P.L.U jM) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) (wVal U (e + 1) y' jL jM) =
      wVal U e y jL jM := by
  have := isLocalRing_quotient_pow (ne_top_of_isHausdorff J) e
  have := fstG_mono (I := I) (G := G) (e + 1)
  have ht := hy.top_le_chart hL hM (show cpt (S ⧸ J ^ (e + 1)) ∈ (⊤ : (Sp (S ⧸ J ^ (e + 1))).Opens) from trivial)
  have e₁ : thickTrans S J e ≫ y' = y ≫ thickMap R I e G := by
    rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, Category.assoc, hy'.1,
      show thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left from thickMap_comp_fGl I e G, hy.1,
      ← Category.assoc, thickTrans_comp]
  have e₂ : Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) (wVal U (e + 1) y' jL jM) =
      wVal U (e + 1) (thickTrans S J e ≫ y') jL jM := (valR_spMap _ y' _ (hy'.top_le_chart hL hM) _).symm
  apply toStkA_injective
  rw [e₂, (hy'.comp (thickTrans S J e)).toStkA_wVal hL hM, hy.toStkA_wVal hL hM, e₁,
    wv_comp_thickMap e y _ jM jL (mem_pull.1 ht.1) (mem_pull.1 ht.2)]

theorem exists_isTau (h : IsFormalPt U J g x) (hL : ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL)
    (hM : ⊤ ≤ basePt g ⁻¹ᵁ D.toPre.P.L.U jM) : ∃ τ : Sˣ, IsTau U J x jL jM τ := by
  choose y hy using h
  have hu : ∀ e, IsUnit (wVal U e (y e) jL jM) := fun e => isUnit_valR _ _ ((hy e).top_le_chart hL hM) _
  have hc := fun e => factor_wVal (hy e) (hy (e + 1)) hL hM
  obtain ⟨a, ha⟩ := exists_unit_limit J (fun e => wVal U e (y e) jL jM) hc hu
  refine ⟨a, fun e xe hxe => ?_⟩
  have := fstG_mono (I := I) (G := G) e
  rw [(cancel_mono _).1 (hxe.trans (hy e).1.symm)]
  exact ha e

theorem isTau_tau (h : IsFormalPt U J g x) (hL : ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL)
    (hM : ⊤ ≤ basePt g ⁻¹ᵁ D.toPre.P.L.U jM) : IsTau U J x jL jM (tau U J x jL jM) := by
  rw [tau, dif_pos (exists_isTau h hL hM)]
  exact (exists_isTau h hL hM).choose_spec

omit [IsLocalRing S] in

theorem IsTau.unique (h : IsFormalPt U J g x) {a b : S} (ha : IsTau U J x jL jM a) (hb : IsTau U J x jL jM b) :
    a = b :=
  eq_of_forall_mk_eq J fun e => by
    obtain ⟨y, hy⟩ := h e
    exact (IsUnit.of_mul_eq_one_right _ (ha e y hy.1)).mul_right_cancel ((ha e y hy.1).trans (hb e y hy.1).symm)

theorem map_tau_mul_wVal (h : IsFormalPt U J g x) (hL : ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL)
    (hM : ⊤ ≤ basePt g ⁻¹ᵁ D.toPre.P.L.U jM) {e : ℕ} {T : Type} [CommRing T] (ρ : S →+* T)
    (hρ : J ^ (e + 1) ≤ RingHom.ker ρ) {xe : Sp T ⟶ (thickObj R I e G).left}
    (hxe : xe ≫ (fstG I e G).left = spMap ρ ≫ x) : ρ (tau U J x jL jM) * wVal U e xe jL jM = 1 := by
  obtain ⟨y, hy⟩ := h e
  have hπ : spMap (Ideal.Quotient.lift _ ρ hρ) ≫ thick S J e = spMap ρ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have := fstG_mono (I := I) (G := G) e
  have e₁ : xe = spMap (Ideal.Quotient.lift _ ρ hρ) ≫ y := by
    rw [← cancel_mono (fstG I e G).left, hxe, Category.assoc, hy.1, ← Category.assoc, hπ]
  have H := congrArg (Ideal.Quotient.lift _ ρ hρ) (isTau_tau h hL hM e y hy.1)
  rw [map_mul, map_one] at H
  rw [e₁]
  exact (congrArg _ (valR_spMap _ y _ (hy.top_le_chart hL hM) _)).trans H

theorem tau_trans (h : IsFormalPt U J g x) (hL : ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL) (hL' : ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL')
    (hM : ⊤ ≤ basePt g ⁻¹ᵁ D.toPre.P.L.U jM) (hM' : ⊤ ≤ basePt g ⁻¹ᵁ D.toPre.P.L.U jM') :
    (tau U J x jL jM).val * valR (basePt g) _ (D.toPre.P.L.g jM jM').val =
      valR x _ (U.LG.L.g jL jL').val * (tau U J x jL' jM').val := by
  refine eq_of_forall_mk_eq J fun e => ?_
  have := isLocalRing_quotient_pow (ne_top_of_isHausdorff J) e
  obtain ⟨y, hy⟩ := h e
  set z := cpt (S ⧸ J ^ (e + 1))
  have m := hy.top_le_chart hL hM (show z ∈ (⊤ : (Sp (S ⧸ J ^ (e + 1))).Opens) from trivial)
  have m' := hy.top_le_chart hL' hM' (show z ∈ (⊤ : (Sp (S ⧸ J ^ (e + 1))).Opens) from trivial)
  have w : wv U e y z jM jL = _ * _ * wv U e y z jM' jL' :=
    gm_isGen (U.w_gen e) y z (fun _ => jM) (fun _ => jM') (fun _ => jL) (fun _ => jL') m.1 m'.1 m.2 m'.2
  rw [gm_pull_g _ _ y z _ _ m.1 m'.1, gm_pull_g _ _ y z _ _ m.2 m'.2, hy.1, hy.2.1] at w
  have t := congrArg (toStkA z) (isTau_tau h hL hM e y hy.1)
  have t' := congrArg (toStkA z) (isTau_tau h hL' hM' e y hy.1)
  rw [map_mul, map_one, hy.toStkA_wVal hL hM] at t
  rw [map_mul, map_one, hy.toStkA_wVal hL' hM'] at t'
  have gM : ⊤ ≤ basePt g ⁻¹ᵁ (D.toPre.P.L.U jM ⊓ D.toPre.P.L.U jM') := fun _ hz => ⟨hM hz, hM' hz⟩
  have gL : ⊤ ≤ x ⁻¹ᵁ (U.LG.L.U jL ⊓ U.LG.L.U jL') := fun _ hz => ⟨hL hz, hL' hz⟩
  apply toStkA_injective
  rw [map_mul, map_mul, map_mul, map_mul, toStkA_map_valR _ _ _ _ gM, toStkA_map_valR _ _ _ _ gL,
    gs_unit _ _ (D.toPre.P.L.U jM ⊓ D.toPre.P.L.U jM') (top_le_comp gM _ trivial),
    gs_unit _ _ (U.LG.L.U jL ⊓ U.LG.L.U jL') (top_le_comp gL _ trivial),
    Units.eq_inv_of_mul_eq_one_right t, Units.eq_inv_of_mul_eq_one_right t', ← Units.val_mul, ← Units.val_mul, w]
  congr 1
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem tau_rig (h : IsFormalPt U J g (s ≫ eSec G)) (hb : basePt g = s ≫ eSec D.toPre.P.A)
    (hL : ⊤ ≤ (s ≫ eSec G) ⁻¹ᵁ U.LG.L.U jL) (hM : ⊤ ≤ basePt g ⁻¹ᵁ D.toPre.P.L.U jM) :
    (tau U J (s ≫ eSec G) jL jM).val *
        valR s ((D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM)) (D.toPre.rig.s (fun _ => jM)).val =
      valR s ((U.LG.L.pull (eSec G)).U (fun _ => jL)) (U.LG.rig.s (fun _ => jL)).val := by
  refine eq_of_forall_mk_eq J fun e => ?_
  have := isLocalRing_quotient_pow (ne_top_of_isHausdorff J) e
  have := fstG_mono (I := I) (G := G) e
  obtain ⟨y, hy⟩ := h e
  set z := cpt (S ⧸ J ^ (e + 1))
  let r : Sp (S ⧸ J ^ (e + 1)) ⟶ Sp (R ⧸ I ^ (e + 1)) := y ≫ pullback.snd G.hom (thick R I e)
  let u : Sp (R ⧸ I ^ (e + 1)) ⟶ (thickObj R I e G).left := eSec (thickObj R I e G)
  have hr : r ≫ thick R I e = thick S J e ≫ s := by
    have e₁ : pullback.snd G.hom (thick R I e) ≫ thick R I e = (fstG I e G).left ≫ G.hom := pullback.condition.symm
    have e₂ : eSec G ≫ G.hom = 𝟙 _ := Over.w η[G]
    rw [Category.assoc, e₁, ← Category.assoc, hy.1, Category.assoc, Category.assoc]
    exact congrArg (thick S J e ≫ ·) ((congrArg (s ≫ ·) e₂).trans (Category.comp_id _))
  have hu : r ≫ u = y := by
    rw [← cancel_mono (fstG I e G).left, hy.1, Category.assoc]
    exact (congrArg (r ≫ ·) (UnitValue.eSec_fGl (G := G) e)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ eSec G) hr).trans (Category.assoc _ _ _)))
  have gM : ⊤ ≤ s ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM) := fun p hp =>
    mem_pull.2 ((congrArg (fun q => q p ∈ D.toPre.P.L.U jM) hb).mp (hM hp))
  have gL : ⊤ ≤ s ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => jL) := fun p hp => mem_pull.2 (hL hp)
  have m₁ : r z ∈ u ⁻¹ᵁ ((D.toPre.P.L.pull (pGl U e)).U (fun _ => jM) ⊓ (U.LG.L.pull (fGl I G e)).U (fun _ => jL)) :=
    (congrArg (fun q => q z ∈ (D.toPre.P.L.pull (pGl U e)).U (fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G e)).U (fun _ => jL)) hu).mpr (hy.top_le_chart hL hM trivial)
  have m₂ : r z ∈ thick R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => jL) :=
    (congrArg (fun q => q z ∈ (U.LG.L.pull (eSec G)).U (fun _ => jL)) hr).mpr (top_le_comp gL _ trivial)
  have m₃ : r z ∈ thick R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM) :=
    (congrArg (fun q => q z ∈ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM)) hr).mpr
      (top_le_comp gM _ trivial)
  have hz : r z ∈ (u ⁻¹ᵁ ((D.toPre.P.L.pull (pGl U e)).U (fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G e)).U (fun _ => jL))) ⊓ thick R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => jL) ⊓
      thick R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM) := ⟨⟨m₁, m₂⟩, m₃⟩
  have W := congrArg (gm r z _) (U.w_rig e (fun _ => jM, fun _ => jL) _
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right)
  have W' : wv U e (r ≫ u) z jM jL * gm (r ≫ thick R I e) z _ (U.LG.rig.s (fun _ => jL)) =
      gm (r ≫ thick R I e) z _ (D.toPre.rig.s (fun _ => jM)) :=
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z _ hz _).trans (gm_pull r u z _ m₁ _))
      ((gm_res r z _ hz _).trans (gm_pull r _ z _ m₂ _)))).symm.trans
      (W.trans ((gm_res r z _ hz _).trans (gm_pull r _ z _ m₃ _)))
  rw [hu, hr] at W'
  have t := congrArg (toStkA z) (isTau_tau h hL hM e y hy.1)
  rw [map_mul, map_one, hy.toStkA_wVal hL hM] at t
  apply toStkA_injective
  rw [map_mul, map_mul, toStkA_map_valR _ _ _ _ gM, toStkA_map_valR _ _ _ _ gL,
    gs_unit _ _ ((D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM)) (top_le_comp gM _ trivial),
    gs_unit _ _ ((U.LG.L.pull (eSec G)).U (fun _ => jL)) (top_le_comp gL _ trivial),
    Units.eq_inv_of_mul_eq_one_right t, ← Units.val_mul]
  exact congrArg Units.val (inv_mul_eq_iff_eq_mul.2 W'.symm)

end Tau

theorem exists_isZero (P : DegPre R) (T : Over (Sp R)) : ∃ g : GtPt P T, g.IsZero := by
  choose t ht vt using fun χ => exists_gen P.P.isLB (φ := PEmpty.elim) (ε := PEmpty.elim)
    (φ' := P.gtφT T (P.zeroT T) χ) (ε' := DegPre.gtε) (fun V _ h => by
      rw [Fintype.prod_empty, Fin.prod_univ_four]
      show 1 = h (P.cT T χ * 1).left ^ (-1 : ℤ) * h (P.cT T χ).left ^ (1 : ℤ) * h (P.zeroT T).left ^ (1 : ℤ) *
        h (P.zeroT T).left ^ (-1 : ℤ)
      simp) (LB.oneGen P.P.L)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  have v : ∀ χ y J, Good P.P.L y J → val (t χ) (𝟙 _) y J = 1 := fun χ y J hJ => (vt χ _ _ y J hJ).trans (val_one _)
  refine ⟨⟨P.zeroT T, t, ht, corr_of_val P.P.isLB fun y J hJ => (v 0 y J hJ).trans (val_one _).symm,
    fun χ χ' => corr_of_val P.P.isLB fun y J hJ => ?_⟩, rfl,
    fun χ => corr_of_val P.P.isLB fun y J hJ => (v χ y J hJ).trans (val_one _).symm⟩
  have c := val_cub P.cub (𝟙 T) hJ (P.cT T χ) (P.cT T χ') (P.zeroT T)
  rw [Category.id_comp, Category.id_comp, Category.id_comp] at c
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  exact congrArg₂ (· * ·) ((v _ y J hJ).trans (v _ y J hJ).symm)
    (c.trans (((isCub_cubV P.cub hJ).face₃ _ _).trans (v _ y J hJ).symm))

variable (U) in

theorem isFormalPt_zero (φ : R →+* S) {g : GtPt D.toPre (Over.mk (spMap φ))} (hg : g.IsZero) :
    IsFormalPt U (I.map φ) g (spMap φ ≫ eSec G) := by
  intro e
  let r : Sp (S ⧸ I.map φ ^ (e + 1)) ⟶ Sp (R ⧸ I ^ (e + 1)) :=
    spMap (Ideal.quotientMap (I.map φ ^ (e + 1)) φ (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map))
  have hr : r ≫ thick R I e = thick S (I.map φ) e ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have hb : basePt g = spMap φ ≫ eSec D.toPre.P.A := by
    refine (congrArg Over.Hom.left hg.1).trans ?_
    exact congrArg (· ≫ eSec D.toPre.P.A) ((Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk (spMap φ)))))
  refine ⟨r ≫ eSec (thickObj R I e G), ?_, ?_, fun χ => corr_of_val D.toPre.P.isLB fun y J hJ => ?_⟩
  · exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (UnitValue.eSec_fGl (G := G) e)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ eSec G) hr).trans (Category.assoc _ _ _))))
  · rw [hb]
    exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (UnitValue.eSec_pGl U e)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ eSec D.toPre.P.A) hr).trans (Category.assoc _ _ _))))
  · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    rw [Category.id_comp, Category.id_comp]
    refine (val_pull hJ _ _ _).symm.trans ((val_corr hJ ((U.gt e).t_unit χ) r).trans ((val_one _).trans ?_))
    exact ((val_corr hJ (hg.2 χ) _).trans (val_one _)).symm

variable (U) in

theorem map_secVal_eq {e k : ℕ} {σ : H0 U.LG.L k} {f : ∀ α : D.toPre.X, D.toPre.SecB k α}
    (h : U.ExpandsAt e k σ f) : ∃ F : Finset D.toPre.X, ∀ (S : Type) [CommRing S] [IsLocalRing S] (J : Ideal S)
      [IsAdicComplete J S] (s : Sp S ⟶ Sp R) (g : GtPt D.toPre (Over.mk s)) (x : Sp S ⟶ G.left),
      IsFormalPt U J g x → ∀ (T : Type) [CommRing T] [IsLocalRing T] (ρ : S →+* T), J ^ (e + 1) ≤ RingHom.ker ρ →
      (∀ α ∉ F, ∀ jf, ⊤ ≤ basePt g ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB α) jf → ρ (famVal g (f α) jf) = 0) ∧
      ∀ (F' : Finset D.toPre.X) (jL : U.LG.L.ι) (jM : D.toPre.P.L.ι) (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι),
        F ⊆ F' → ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL → ⊤ ≤ basePt g ⁻¹ᵁ D.toPre.P.L.U jM →
        (∀ α ∈ F', CohCharts g α jM (jf α) (jt α)) →
        ρ (secVal U σ x jL) =
          ρ ((tau U J x jL jM).val ^ k * ∑ α ∈ F', famVal g (f α) (jf α) * coordVal g α (jt α)) := by
  obtain ⟨F, hF⟩ := expandsAt_value U h
  refine ⟨F, fun S _ _ J _ s g x hx T _ _ ρ hρ => ?_⟩
  obtain ⟨y, hy⟩ := hx e
  have hπ : spMap (Ideal.Quotient.lift _ ρ hρ) ≫ thick S J e = spMap ρ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have H := hπ ▸ hy.comp (spMap (Ideal.Quotient.lift _ ρ hρ))
  obtain ⟨h₀, h₁⟩ := hF S s g x T ρ _ H
  refine ⟨h₀, fun F' jL jM jf jt hFF hL hM hc => ?_⟩
  have e₁ : ρ (∑ α ∈ F', famVal g (f α) (jf α) * coordVal g α (jt α)) =
      ρ (∑ α ∈ F, famVal g (f α) (jf α) * coordVal g α (jt α)) := by
    rw [map_sum, map_sum]
    refine (Finset.sum_subset hFF fun α hα hα' => ?_).symm
    rw [map_mul, h₀ α hα' _ (hc α hα).1, zero_mul]
  rw [map_mul, e₁, ← h₁ jL jM jf jt hL hM fun α hα => hc α (hFF hα), map_pow, ← _root_.mul_assoc, ← mul_pow,
    map_tau_mul_wVal hx hL hM ρ hρ H.1, one_pow, _root_.one_mul]

variable (U) in

theorem expansion_unique [IsNoetherianRing R] [IsAdicComplete I R] {k : ℕ} {σ : H0 U.LG.L k}
    {f f' : ∀ α : D.toPre.X, D.toPre.SecB k α} (h : ∀ e, U.ExpandsAt e k σ f) (h' : ∀ e, U.ExpandsAt e k σ f') :
    f = f' := by
  have := D.toPre.P.isAb.proper
  let d : ∀ α : D.toPre.X, D.toPre.SecB k α := fun α => SecOps.secAdd (f α) (SecOps.secNeg (f' α))
  have hd : ∀ e, U.ExpandsAt e k SecOps.secZero d := fun e =>
    expandsAt_sub R I D A G U e k σ σ _ f f' d (fun j => (sub_self _).symm)
      (fun α j => (sub_eq_add_neg _ _).symm) (h e) (h' e)
  funext α
  refine SecOps.sec_ext fun j => sub_eq_zero.1 ((sub_eq_add_neg _ _).trans ?_)
  refine sec_eq_zero_of_thickenings I (IsAdicComplete.le_jacobson_bot I) D.toPre.P.A (d α) (fun y => ?_)
    (fun e j => (ExtDiv.pG_app_eq_zero_iff (U.gt e) _ _).1
      (WeightPf.weightIndep R I D A G U e k _ d (fun _ => map_zero _) (hd e) α j)) j
  choose i hi using fun a => exists_chart D.toPre.P.isLB (D.toPre.famφB α a y)
  exact ⟨i, Set.mem_iInter.2 hi⟩

end Formal

theorem value_eq_sum_expansion {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I)
    {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G)
    {S : Type} [CommRing S] [Algebra R S] [IsLocalRing S] [IsAdicComplete (I.map (algebraMap R S)) S]
    (g : GtPt D.toPre (Over.mk (spMap (algebraMap R S)))) (x : Sp S ⟶ G.left)
    (hx : IsFormalPt U.toUnifPre (I.map (algebraMap R S)) g x) :
    (∀ jL jM, ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL → ⊤ ≤ basePt g ⁻¹ᵁ D.toPre.P.L.U jM →
      (∀ τ : S, IsTau U.toUnifPre (I.map (algebraMap R S)) x jL jM τ ↔
        τ = tau U.toUnifPre (I.map (algebraMap R S)) x jL jM) ∧
      (∀ jL' jM', ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL' → ⊤ ≤ basePt g ⁻¹ᵁ D.toPre.P.L.U jM' →
        (tau U.toUnifPre (I.map (algebraMap R S)) x jL jM).val * valR (basePt g) _ (D.toPre.P.L.g jM jM').val =
          valR x _ (U.LG.L.g jL jL').val * (tau U.toUnifPre (I.map (algebraMap R S)) x jL' jM').val) ∧
      ∀ α, ∃ jf jt, CohCharts g α jM jf jt) ∧
    ∀ (k : ℕ) (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ f) →
      (∀ e, ∃ F : Finset D.toPre.X,
        (∀ α ∉ F, ∀ jf, ⊤ ≤ basePt g ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB α) jf →
          famVal g (f α) jf ∈ I.map (algebraMap R S) ^ (e + 1)) ∧
        ∀ (F' : Finset D.toPre.X) (jL : U.LG.L.ι) (jM : D.toPre.P.L.ι) (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι),
          F ⊆ F' → ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL → ⊤ ≤ basePt g ⁻¹ᵁ D.toPre.P.L.U jM →
          (∀ α ∈ F', CohCharts g α jM (jf α) (jt α)) →
          secVal U.toUnifPre σ x jL - (tau U.toUnifPre (I.map (algebraMap R S)) x jL jM).val ^ k *
            ∑ α ∈ F', famVal g (f α) (jf α) * coordVal g α (jt α) ∈ I.map (algebraMap R S) ^ (e + 1)) ∧
      ∀ f' : ∀ α : D.toPre.X, D.toPre.SecB k α, (∀ e, U.ExpandsAt e k σ f') → f = f' := by
  have := hR.1
  have := hR.2.2.2
  refine ⟨fun jL jM hL hM => ⟨fun τ => ⟨fun h => IsTau.unique hx h (isTau_tau hx hL hM),
    fun h => h ▸ isTau_tau hx hL hM⟩, fun jL' jM' hL' hM' => tau_trans hx hL hL' hM hM',
    exists_cohCharts g jM hM⟩, fun k σ f h => ⟨fun e => ?_, fun f' h' => expansion_unique U.toUnifPre h h'⟩⟩
  have := isLocalRing_quotient_pow (ne_top_of_isHausdorff (I.map (algebraMap R S))) e
  obtain ⟨F, hF⟩ := map_secVal_eq U.toUnifPre (h e)
  obtain ⟨h₀, h₁⟩ := hF S _ _ g x hx _ (Ideal.Quotient.mk (I.map (algebraMap R S) ^ (e + 1))) Ideal.mk_ker.ge
  exact ⟨F, fun α hα jf hj => Ideal.Quotient.eq_zero_iff_mem.1 (h₀ α hα jf hj),
    fun F' jL jM jf jt a b c d => Ideal.Quotient.eq.1 (h₁ F' jL jM jf jt a b c d)⟩

end GlobalTheory.FormalValue
